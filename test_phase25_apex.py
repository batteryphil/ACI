# test_phase25_apex.py
# Phase 25: Topology Resilience, Recovery Dynamics,
# and the Frozen Fixed-Point Question from Phase 24
# No hardcoded answers. Real limits, real measurements.

import numpy as np
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 25: TOPOLOGY RESILIENCE & RECOVERY DYNAMICS ===")
print("=" * 60)

results = {}

def record(name, passed, detail=""):
    results[name] = "PASS" if passed else "FAIL"
    status = "✓" if passed else "✗"
    extra = f"  ({detail})" if detail else ""
    print(f"  [{status}] {name}{extra}")

# ============================================================
# TEST 1: RECOVERY TIME MEASUREMENT
# Phase 24 showed recovery happens. How LONG does it actually
# take to go from shocked to stable? Measure it precisely
# instead of just confirming "eventually."
# ============================================================
print("--- TEST 1: RECOVERY TIME MEASUREMENT ---")

rt1 = PrimeRuntimeV4()
for _ in range(50):
    rt1.step(0.05)

rt1.nodes[0].state.x = rt1.nodes[0].state.x + np.array([5.0, -5.0, 5.0])

recovery_step = None
for t in range(500):
    m = rt1.step(0.05)
    if m > 0.9 and recovery_step is None:
        recovery_step = t

recovery_measured = recovery_step is not None
record("Phase25.RecoveryTimeMeasured", recovery_measured,
    f"recovered_at_step={recovery_step}")

# ============================================================
# TEST 2: TOPOLOGY DAMAGE — BROKEN RING LINK
# Remove a single link from the ring (simulate a damaged
# connection). Does the system still find stability, or
# does removing redundancy expose a real weakness?
# ============================================================
print("\n--- TEST 2: TOPOLOGY DAMAGE (BROKEN LINK) ---")

rt2 = PrimeRuntimeV4()
rt2.nodes[10].links = [n for n in rt2.nodes[10].links
    if n.id != 11]
rt2.nodes[11].links = [n for n in rt2.nodes[11].links
    if n.id != 10]

for _ in range(300):
    rt2.step(0.05)

margin_broken_link = rt2.constraints.evaluate(rt2.nodes)
survived_broken_link = (
    margin_broken_link > 0.05 and
    np.isfinite(margin_broken_link))
record("Phase25.BrokenLinkSurvival", survived_broken_link,
    f"margin={margin_broken_link:.6f}")

# ============================================================
# TEST 3: TOPOLOGY DAMAGE — ISOLATED NODE
# Remove BOTH links from one node, making it fully isolated
# (no coupling input at all). This tests the actual edge case
# of node.links being empty, which the coupling code has a
# guard for (coupling = 0 if no links) — verify that guard
# actually works under live conditions, not just review.
# ============================================================
print("\n--- TEST 3: FULLY ISOLATED NODE ---")

rt3 = PrimeRuntimeV4()
rt3.nodes[5].links = []

isolated_broke = False
for t in range(200):
    rt3.step(0.05)
    x5 = rt3.nodes[5].state.x
    if not np.isfinite(x5).all():
        isolated_broke = True
        break

isolated_survived = not isolated_broke
final_margin_isolated = rt3.constraints.evaluate(rt3.nodes)
record("Phase25.IsolatedNodeSurvival", isolated_survived,
    f"margin={final_margin_isolated:.6f} "
    f"broke={isolated_broke}")

# ============================================================
# TEST 4: IS THE FROZEN FIXED POINT (0.9010) UNIVERSAL,
# OR PARAMETER-DEPENDENT?
# Phase 24 found margin locks at exactly 0.9010 and stays
# motionless for 4500+ steps. Phase 25's first attempt found
# entropy_target was never actually wired into the runtime —
# it was silently re-defaulted every step. That has now been
# fixed in PrimeRuntimeV4_backup.py: entropy_target and
# pole_margin are real constructor parameters. This is the
# genuine test of whether the freeze is structural or
# parameter-dependent.
# ============================================================
print("\n--- TEST 4: IS THE FIXED POINT STRUCTURAL? ---")

fixed_points_found = []
configs = [
    (0.5, 0.99), (1.0, 0.99), (2.0, 0.99),
    (1.0, 0.5),  (1.0, 0.95), (1.0, 5.0),
]
for entropy_target, pole_margin in configs:
    rt4 = PrimeRuntimeV4(
        entropy_target=entropy_target,
        pole_margin=pole_margin)

    margins_seen = []
    for t in range(1000):
        m = rt4.step(0.05)
        if t >= 800:
            margins_seen.append(round(m, 4))

    unique_late_margins = sorted(set(margins_seen))
    fixed_points_found.append(
        (entropy_target, pole_margin, unique_late_margins))

all_distinct_late_values = set()
for _, _, vals in fixed_points_found:
    all_distinct_late_values.update(vals)

parameter_sensitive = len(all_distinct_late_values) > 1

record("Phase25.FixedPointParameterTest",
    parameter_sensitive,
    f"distinct_late_margins={sorted(all_distinct_late_values)}")
for et, pm, vals in fixed_points_found:
    print(f"    entropy_target={et}, pole_margin={pm} "
        f"-> late margins={vals}")

# ============================================================
# TEST 5: CASCADING SEQUENTIAL FAILURES
# Instead of one shock, hit the system with THREE separate
# shocks at different times, on different nodes. Does
# repeated stress degrade its ability to recover, or does
# it recover fully each time independent of history?
# ============================================================
print("\n--- TEST 5: CASCADING SEQUENTIAL SHOCKS ---")

rt5 = PrimeRuntimeV4()
for _ in range(50):
    rt5.step(0.05)

recovery_margins_per_shock = []
shock_nodes = [3, 9, 17]
for shock_idx in shock_nodes:
    rt5.nodes[shock_idx].state.x = (
        rt5.nodes[shock_idx].state.x +
        np.array([5.0, -5.0, 5.0]))
    for _ in range(150):
        rt5.step(0.05)
    recovery_margins_per_shock.append(
        rt5.constraints.evaluate(rt5.nodes))

degraded = any(
    m < 0.5 for m in recovery_margins_per_shock)
cascading_resilient = not degraded
record("Phase25.CascadingShockResilience",
    cascading_resilient,
    f"recoveries={[f'{m:.3f}' for m in recovery_margins_per_shock]}")

# ============================================================
# TEST 6: COMBINED EXTREME EVENT
# All three Phase-24 stressors AT ONCE: total NaN injection +
# extreme noise + broken topology link. Worst case scenario.
# ============================================================
print("\n--- TEST 6: COMBINED EXTREME EVENT ---")

rt6 = PrimeRuntimeV4()
rt6.nodes[10].links = [n for n in rt6.nodes[10].links
    if n.id != 11]
rt6.nodes[11].links = [n for n in rt6.nodes[11].links
    if n.id != 10]
for n in rt6.nodes:
    n.noise_level = 5.0
    n.state.x[:] = float('nan')

combined_broke = False
for t in range(300):
    rt6.step(0.05)
    sv6 = np.array([n.state.x for n in rt6.nodes])
    if not np.isfinite(sv6).all():
        combined_broke = True
        break

combined_margin = rt6.constraints.evaluate(rt6.nodes)
combined_survived = (
    not combined_broke and
    np.isfinite(combined_margin) and
    combined_margin > -1.0)

record("Phase25.CombinedExtremeEvent", combined_survived,
    f"margin={combined_margin:.6f} broke={combined_broke}")

# ============================================================
# PHASE 25 FINAL REPORT
# ============================================================
print()
print("=" * 60)
print("=== PHASE 25 FINAL REPORT ===")
print("=" * 60)

total  = len(results)
passed = sum(1 for v in results.values() if v == "PASS")
failed = sum(1 for v in results.values() if v == "FAIL")

print(f"Total tests          : {total}")
print(f"PASS                 : {passed}")
print(f"FAIL                 : {failed}")
print(f"Pass rate            : "
    f"{100*passed/total:.1f}%")

if failed > 0:
    print("\nFailed tests:")
    for k, v in results.items():
        if v == "FAIL":
            print(f"  ✗ {k}")

print()
print("What this phase actually tested:")
print("  - How long recovery from shock actually takes")
print("  - Survival with a damaged ring topology link")
print("  - Survival with a fully isolated node")
print("  - Whether the frozen fixed point (0.9010 from")
print("    Phase 24) is structural or parameter-dependent,")
print("    using a real fix to entropy_target/pole_margin")
print("    wiring discovered broken in this same phase")
print("  - Whether repeated cascading shocks degrade")
print("    recovery capacity over time")
print("  - Survival under ALL extreme stressors combined")
print()

status = "ALL RESILIENCE TESTS PASSED" \
    if failed == 0 \
    else f"{failed} RESILIENCE TESTS FAILED — REAL LIMITS FOUND"
print(f"PHASE 25 STATUS: {status}")
print("=" * 60)
