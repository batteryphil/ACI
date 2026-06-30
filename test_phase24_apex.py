# test_phase24_apex.py
# Phase 24: Stress, Perturbation, and Limit Testing
# No hardcoded answers. Tests what the system can ACTUALLY do,
# not just confirms what it already showed in Phase 22/23.

import numpy as np
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 24: STRESS, PERTURBATION, LIMIT TESTING ===")
print("Testing robustness, not just stability confirmation.")
print("=" * 60)

rt = PrimeRuntimeV4()
results = {}

def sv():
    return np.array([n.state.x for n in rt.nodes])

def step(n=5, dt=0.05):
    for _ in range(n):
        rt.step(dt)

def margin():
    return rt.constraints.evaluate(rt.nodes)

def norms():
    return np.array([
        np.linalg.norm(n.state.x)
        for n in rt.nodes])

def energy():
    return float(np.sum(sv()**2))

def record(name, passed, detail=""):
    results[name] = "PASS" if passed else "FAIL"
    status = "✓" if passed else "✗"
    extra = f"  ({detail})" if detail else ""
    print(f"  [{status}] {name}{extra}")

# Warmup
step(50)
print(f"\nBaseline established:")
print(f"  Margin : {margin():.6f}")
print(f"  Energy : {energy():.6f}\n")

# ============================================================
# TEST 1: PERTURBATION RECOVERY
# Inject a large shock into one node, see if the system
# recovers margin/stability afterward, unassisted.
# ============================================================
print("--- TEST 1: PERTURBATION RECOVERY ---")

margin_before = margin()
shock_node = rt.nodes[0]
shock_node.state.x = shock_node.state.x + np.array([5.0, -5.0, 5.0])
margin_immediately_after = margin()

step(100)
margin_recovered = margin()

recovered = margin_recovered > 0.5
record("Phase24.PerturbationRecovery", recovered,
    f"before={margin_before:.3f} "
    f"shock={margin_immediately_after:.3f} "
    f"recovered={margin_recovered:.3f}")

# ============================================================
# TEST 2: SENSITIVITY TO INITIAL CONDITIONS
# Run two independent instances with different seeds,
# check whether trajectories diverge meaningfully
# (real chaos/sensitivity signature) or stay locked together.
# ============================================================
print("\n--- TEST 2: SENSITIVITY TO INITIAL CONDITIONS ---")

np.random.seed(1)
rt_a = PrimeRuntimeV4()
np.random.seed(2)
rt_b = PrimeRuntimeV4()

for _ in range(300):
    rt_a.step(0.05)
    rt_b.step(0.05)

sv_a = np.array([n.state.x for n in rt_a.nodes])
sv_b = np.array([n.state.x for n in rt_b.nodes])
divergence = float(np.linalg.norm(sv_a - sv_b))

# Genuine test: divergence should be measurable (not zero,
# meaning seeds matter) but bounded (not exploding,
# meaning the system doesn't blow up under different inits)
sensitivity_real = divergence > 1e-6
sensitivity_bounded = divergence < 50.0
record("Phase24.SensitivityNonzero", sensitivity_real,
    f"divergence={divergence:.6f}")
record("Phase24.SensitivityBounded", sensitivity_bounded,
    f"divergence={divergence:.6f}")

# ============================================================
# TEST 3: LONG-HORIZON STABILITY (5000 STEPS)
# Does the system actually stay stable over a much longer
# run than any previous phase tested?
# ============================================================
print("\n--- TEST 3: LONG-HORIZON STABILITY (5000 STEPS) ---")

rt_long = PrimeRuntimeV4()
margins_over_time = []
min_margin_seen = 1.0
instability_detected_at = None

for t in range(5000):
    m = rt_long.step(0.05)
    if t % 500 == 0:
        margins_over_time.append(m)
    if m <= 0.05 and instability_detected_at is None:
        instability_detected_at = t
    min_margin_seen = min(min_margin_seen, m)

long_horizon_stable = instability_detected_at is None
record("Phase24.LongHorizon5000Steps", long_horizon_stable,
    f"min_margin={min_margin_seen:.4f} "
    f"instability_at={instability_detected_at}")

print(f"    Margin samples: "
    f"{[f'{m:.4f}' for m in margins_over_time]}")

# ============================================================
# TEST 4: EXTREME NOISE INJECTION
# Push noise_level far beyond normal operating range,
# see if pole-stabilization and clamps actually hold,
# or if the system genuinely breaks.
# ============================================================
print("\n--- TEST 4: EXTREME NOISE INJECTION ---")

rt_noise = PrimeRuntimeV4()
for n in rt_noise.nodes:
    n.noise_level = 5.0  # 500x normal (0.01)

broke = False
max_norm_seen = 0.0
for t in range(200):
    rt_noise.step(0.05)
    ns = np.array([
        np.linalg.norm(n.state.x)
        for n in rt_noise.nodes])
    max_norm_seen = max(max_norm_seen, float(ns.max()))
    if not np.isfinite(ns).all():
        broke = True
        break

extreme_noise_survived = not broke
record("Phase24.ExtremeNoiseInjection",
    extreme_noise_survived,
    f"max_norm={max_norm_seen:.4f} broke={broke}")

# ============================================================
# TEST 5: GENUINE NODE DIFFERENTIATION
# Question raised earlier: do the 21 nodes EVER behave
# differently, or does the clamp always force identical
# output? Test under conditions designed to differentiate
# them (different link topology stress).
# ============================================================
print("\n--- TEST 5: NODE DIFFERENTIATION UNDER ASYMMETRIC STRESS ---")

rt_diff = PrimeRuntimeV4()
# Shock only nodes 0, 7, 14 — asymmetric perturbation
for idx in [0, 7, 14]:
    rt_diff.nodes[idx].state.x = (
        rt_diff.nodes[idx].state.x +
        np.array([3.0, 3.0, 3.0]))

step_results = []
for _ in range(20):
    rt_diff.step(0.05)
    ns = np.array([
        np.linalg.norm(n.state.x)
        for n in rt_diff.nodes])
    step_results.append(ns.copy())

step_results = np.array(step_results)
# Check variance ACROSS nodes at each timestep right after
# the shock — if real, shocked nodes should show elevated
# norms before clamp pulls everything to 0.99
early_spread = float(np.std(step_results[0]))
late_spread = float(np.std(step_results[-1]))

differentiation_existed = early_spread > 1e-4
record("Phase24.NodeDifferentiationDetected",
    differentiation_existed,
    f"early_spread={early_spread:.6f} "
    f"late_spread={late_spread:.6f}")

# ============================================================
# TEST 6: RECOVERY FROM TOTAL NaN INJECTION
# Inject NaN into ALL 21 nodes simultaneously (not just one,
# like prior phase tests), see if recovery still works
# at full-system scale.
# ============================================================
print("\n--- TEST 6: TOTAL NaN INJECTION (ALL 21 NODES) ---")

rt_nan = PrimeRuntimeV4()
for n in rt_nan.nodes:
    n.state.x[:] = float('nan')

out = rt_nan.step(0.05)
sv_nan_check = np.array([
    n.state.x for n in rt_nan.nodes])
all_finite_after_one_step = np.isfinite(sv_nan_check).all()

step(20, dt=0.05) if False else None  # no-op guard
for _ in range(20):
    rt_nan.step(0.05)

sv_nan_final = np.array([
    n.state.x for n in rt_nan.nodes])
all_finite_final = np.isfinite(sv_nan_final).all()
final_margin_nan = rt_nan.constraints.evaluate(rt_nan.nodes)

record("Phase24.TotalNaNRecovery",
    all_finite_after_one_step and all_finite_final,
    f"finite_immediately={all_finite_after_one_step} "
    f"finite_after_20={all_finite_final} "
    f"margin={final_margin_nan:.4f}")

# ============================================================
# PHASE 24 FINAL REPORT
# ============================================================
print()
print("=" * 60)
print("=== PHASE 24 FINAL REPORT ===")
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
print("  - Recovery from large single-node shock")
print("  - Sensitivity to initial conditions (seed dependence)")
print("  - Stability over 5000 steps (10x prior longest test)")
print("  - Survival under 500x normal noise injection")
print("  - Whether nodes EVER differentiate under stress")
print("  - Recovery from simultaneous total-system NaN")
print()

status = "ALL STRESS TESTS PASSED" \
    if failed == 0 \
    else f"{failed} STRESS TESTS FAILED — REAL LIMITS FOUND"
print(f"PHASE 24 STATUS: {status}")
print("=" * 60)
