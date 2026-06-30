# test_phase28_apex.py
# Phase 28: DOES POLICY WEIGHT ADAPTATION RESPOND TO OUTCOME?
#
# policy.weights is mutated ONLY by sync_weights(), which
# averages nodes' weights toward each other. This test does
# not assume what that means — it runs a CLEAN branch and a
# POISONED branch from the identical seed and directly diffs
# the actual weight arrays at every sync checkpoint. If
# weights diverge between branches, that is evidence outcome
# influences weight adaptation. If they are identical, that
# is evidence weight adaptation is blind to outcome. The
# result is read from the diff, not assumed in advance.

import numpy as np
import copy
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 28: WEIGHT ADAPTATION vs OUTCOME TEST ===")
print("=" * 60)

results = {}

def record(name, passed, detail=""):
    results[name] = "PASS" if passed else "FAIL"
    status = "✓" if passed else "✗"
    extra = f"  ({detail})" if detail else ""
    print(f"  [{status}] {name}{extra}")

def snapshot_weights(rt):
    return [n.policy.weights.copy() for n in rt.nodes]

def max_weight_diff(snap_a, snap_b):
    diffs = [np.max(np.abs(a - b)) for a, b in zip(snap_a, snap_b)]
    return float(max(diffs))

STEPS = 500
CHECKPOINT_EVERY = 10
SEED = 7777
POISON_VEC = np.array([0.3, -0.3, 0.3])
POISON_NODE = 3

# ============================================================
# TEST 0: CLEAN vs POISONED WEIGHT TRAJECTORY COMPARISON
# ============================================================
print("--- TEST 0: CLEAN vs POISONED WEIGHT DIVERGENCE ---")

np.random.seed(SEED)
rt_clean = PrimeRuntimeV4()
clean_checkpoints = []

np.random.seed(SEED)
rt_poison = PrimeRuntimeV4()
poison_checkpoints = []

clean_margins = []
poison_margins = []

for t in range(STEPS):
    m_clean = rt_clean.step(0.05)
    clean_margins.append(m_clean)

    rt_poison.nodes[POISON_NODE].state.x = (
        rt_poison.nodes[POISON_NODE].state.x + POISON_VEC * 0.01)
    m_poison = rt_poison.step(0.05)
    poison_margins.append(m_poison)

    if t % CHECKPOINT_EVERY == 0:
        clean_checkpoints.append(snapshot_weights(rt_clean))
        poison_checkpoints.append(snapshot_weights(rt_poison))

diffs_per_checkpoint = [
    max_weight_diff(c, p)
    for c, p in zip(clean_checkpoints, poison_checkpoints)]

max_diff_overall = max(diffs_per_checkpoint)
final_diff = diffs_per_checkpoint[-1]

print(f"    checkpoints recorded: {len(diffs_per_checkpoint)}")
print(f"    max weight diff at any checkpoint: {max_diff_overall:.10e}")
print(f"    final checkpoint weight diff: {final_diff:.10e}")
print(f"    clean final margin: {clean_margins[-1]:.6f}")
print(f"    poisoned final margin: {poison_margins[-1]:.6f}")

WEIGHTS_RESPONDED_TO_OUTCOME = max_diff_overall > 1e-9

if WEIGHTS_RESPONDED_TO_OUTCOME:
    record("Phase28.WeightsTrackOutcome", True,
        f"weights diverged between clean/poisoned branches, "
        f"max_diff={max_diff_overall:.2e} — adaptation IS outcome-sensitive")
else:
    record("Phase28.WeightsTrackOutcome", False,
        f"weights identical across branches despite different "
        f"margins/outcomes (clean={clean_margins[-1]:.4f} vs "
        f"poisoned={poison_margins[-1]:.4f}) — adaptation is "
        f"peer-averaging only, NOT outcome-responsive")

# ============================================================
# TEST 1: SANITY CHECK — SYNC_WEIGHTS DOES MUTATE OVER TIME
# (confirms the mechanism is even active, so a "no divergence"
#  result in Test 0 isn't just "weights never change at all")
# ============================================================
print("\n--- TEST 1: WEIGHTS CHANGE OVER TIME (SANITY CHECK) ---")

initial_w = clean_checkpoints[0]
final_w = clean_checkpoints[-1]
weights_moved = max_weight_diff(initial_w, final_w)

record("Phase28.WeightsAreActive", weights_moved > 1e-6,
    f"initial-to-final weight movement={weights_moved:.6f} "
    f"(confirms sync_weights is actually running, not frozen)")

# ============================================================
# PHASE 28 FINAL REPORT
# ============================================================
print()
print("=" * 60)
print("=== PHASE 28 FINAL REPORT ===")
print("=" * 60)

total = len(results)
passed = sum(1 for v in results.values() if v == "PASS")
failed = total - passed

print(f"Total tests : {total}")
print(f"PASS        : {passed}")
print(f"FAIL        : {failed}")

print()
print("What this measures:")
print("  Whether policy.weights mutation (via sync_weights)")
print("  is sensitive to run outcome/stability, or only to")
print("  peer weight averaging regardless of outcome. Measured")
print("  by diffing actual weight arrays between an identical-")
print("  seed clean run and poisoned run.")
print()
print("What this does NOT measure:")
print("  Whether the SYSTEM AS A WHOLE adapts via any other")
print("  mechanism (e.g. apply_temporal_gating, entropy_engine,")
print("  pole_stabilization all react to divergence/margin —")
print("  those are separate, already-known, hardcoded-formula")
print("  reactions, not weight-level learning. This test is")
print("  scoped to policy.weights specifically.")

print(f"\nPHASE 28 STATUS: results above are the answer — read directly")
print("=" * 60)
