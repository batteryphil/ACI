# test_phase30_apex.py
# Phase 30: COMPUTE -> BRANCH -> CONSTRUCT REMEDIATION
# Ports the structural pattern from Optimus7.pure_post_measurement_state
# (compute quantity from live state -> branch on sign -> construct new
# object, carrying proof-relevant properties forward) into the runtime.
# Applied here to fault recovery rather than quantum measurement.
#
# No hardcoded pass/fail label -- raw counts only, read directly.

import numpy as np
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 30: COMPUTE-BRANCH-CONSTRUCT REMEDIATION ===")
print("=" * 60)

def recovery_feasibility(node):
    """
    The 'prob' analogue: a single computed quantity from live
    state. Positive = remediation should be attempted.
    Built from local_margin (existing) and current load.
    """
    s = node.state
    return s.local_margin - 0.5 * s.load

def attempt_remediation(node):
    """
    compute -> branch -> construct, same shape as
    pure_post_measurement_state. Returns the constructed
    corrected node-state dict if feasibility > 0, else None.
    """
    feas = recovery_feasibility(node)
    if feas > 0:
        s = node.state
        corrected_mass = max(node.mass, 0.01)
        corrected_x = s.x * 0.9
        return {
            "feasible": True,
            "feasibility_score": feas,
            "corrected_mass": corrected_mass,
            "corrected_x_norm": float(np.linalg.norm(corrected_x)),
        }
    return None

def apply_remediation(node, result):
    if result is None:
        return False
    node.mass = result["corrected_mass"]
    node.state.x = node.state.x * 0.9
    return True

# ============================================================
# TEST 0: DOES REMEDIATION RESTORE STABILITY AFTER FAULT?
# ============================================================
print("--- TEST 0: FAULT -> REMEDIATE -> RECOVERY CHECK (25 trials) ---")

N_TRIALS = 25
recovered = 0
not_attempted = 0
attempted_but_failed = 0
trial_log = []

for trial in range(N_TRIALS):
    rng = np.random.default_rng(7000 + trial)
    np.random.seed(7000 + trial)
    rt = PrimeRuntimeV4()

    warmup = int(rng.integers(10, 60))
    for _ in range(warmup):
        rt.step(0.05)

    target_id = int(rng.integers(0, 21))
    rt.nodes[target_id].mass = float(rng.uniform(0.0005, 0.002))

    margin_at_fault = None
    for t in range(100):
        m = rt.step(0.05)
        if rt.nodes[target_id].state.n7_gate_status == "Vetoed":
            margin_at_fault = m
            break

    result = attempt_remediation(rt.nodes[target_id])
    applied = apply_remediation(rt.nodes[target_id], result)

    for t in range(100):
        rt.step(0.05)

    cleared = rt.nodes[target_id].state.n7_gate_status == "Sealed"

    if not applied:
        not_attempted += 1
        outcome = "NOT_ATTEMPTED"
    elif cleared:
        recovered += 1
        outcome = "RECOVERED"
    else:
        attempted_but_failed += 1
        outcome = "ATTEMPTED_NO_RECOVERY"

    trial_log.append((trial, target_id, applied, cleared, outcome))

for trial, target_id, applied, cleared, outcome in trial_log:
    print(f"    trial={trial} target={target_id} "
          f"remediation_applied={applied} cleared={cleared} {outcome}")

print(f"\n    RECOVERED={recovered}/{N_TRIALS} "
      f"NOT_ATTEMPTED={not_attempted}/{N_TRIALS} "
      f"ATTEMPTED_NO_RECOVERY={attempted_but_failed}/{N_TRIALS}")
print("    (raw result -- no pass/fail label, read the counts directly)")

print()
print("=" * 60)
print("What this measures: a compute->branch->construct mechanism,")
print("structurally ported from Optimus7's measurement-state pattern,")
print("applied to fault recovery. Does computing a feasibility score")
print("and conditionally constructing a corrected state actually")
print("restore stability, measured directly.")
print()
print("What this does NOT measure: the branch condition and")
print("correction formula are still hand-written by us, same as")
print("every prior phase. The system does not derive what to check")
print("or how to correct -- it executes a richer, written branch.")
print("=" * 60)
