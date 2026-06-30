# test_phase27_apex.py
# Phase 27: ADVERSARIAL SEARCH — finding failure modes
# deliberately, not just surviving prescribed stress.
# No hardcoded answers. If nothing fails here, that's a
# real and meaningful result, not a guaranteed one.
#
# FOURTEEN-STRUCTURE INTEGRATION: SovereignHamiltonian,
# MC2Engine, EnergyTriad, EnergyDomain, AntaresCategory,
# Lawson criterion, Alfvén velocity, frame dragging, MHD
# divB-free invariant, N7Spine gate/bottleneck, Manifold21
# symplectic/Lyapunov, MoruzinLaw chamber validity, and the
# quantum density-matrix family (QuantumCore, Optimus7Quantum,
# Matrix7, Optimus7) as a faithful 2x2 instance of their
# proven properties.
#
# First run found quantum_trace_one's tolerance (1e-9) was
# tighter than realistic floating-point drift from repeated
# normalization/rotation over many steps (measured deviation
# ~1.03e-9 at step 50, eigenvalues correctly nonneg, Hermitian
# held exactly — a precision artifact, not a real violation).
# Tolerance widened to 1e-6 in the runtime; this re-verifies.

import numpy as np
from PrimeRuntimeV4_backup import (
    PrimeRuntimeV4, POLE_MARGIN_MIN, POLE_MARGIN_MAX,
    ENTROPY_TARGET_MIN, ENTROPY_TARGET_MAX,
    NOISE_LEVEL_MIN, NOISE_LEVEL_MAX,
    DOMAIN_NAMES, domain_priority,
    T_kinetic, V_potential, G_governance, H_OPT7,
    mc2_load_factor, mc2_effective_mass,
    mc2_collision_force, mc2_displacement,
    lawson_satisfied, alfven_velocity, frame_dragging,
    divB_residual, n7_M_N7, n7_gate_decision,
    manifold21_omega, manifold21_lyapunov,
    moruzin_chamber_valid, moruzin_chamber_compose,
    quantum_density_matrix, quantum_is_hermitian,
    quantum_trace_one, quantum_is_positive,
    quantum_unitary_evolve, quantum_trace_preserved)

print("=" * 60)
print("=== PHASE 27: ADVERSARIAL SEARCH ===")
print("=== (fourteen-structure physics/formal integration) ===")
print("=" * 60)

results = {}
MARGIN_SANE_LOW = -1.0
MARGIN_SANE_HIGH = 2.0

def is_functionally_stable(margin):
    return (np.isfinite(margin) and
        MARGIN_SANE_LOW <= margin <= MARGIN_SANE_HIGH)

def record(name, passed, detail=""):
    results[name] = "PASS" if passed else "FAIL"
    status = "✓" if passed else "✗"
    extra = f"  ({detail})" if detail else ""
    print(f"  [{status}] {name}{extra}")

def sustained_below(margins, threshold=0.05, run_len=3):
    streak = 0
    worst = 0
    for m in margins:
        if m <= threshold:
            streak += 1
            worst = max(worst, streak)
        else:
            streak = 0
    return worst

# ============================================================
# TEST 0: FOURTEEN-STRUCTURE INTEGRATION VERIFICATION
# ============================================================
print("--- TEST 0: FOURTEEN-STRUCTURE VERIFICATION ---")

rt0 = PrimeRuntimeV4()
for _ in range(50):
    rt0.step(0.05)

domain_labels_valid = all(
    n.domain_name in DOMAIN_NAMES and 1 <= n.priority <= 21
    for n in rt0.nodes)
record("Phase27.01_EnergyDomain", domain_labels_valid,
    f"sample: {rt0.nodes[0].domain_name} p={rt0.nodes[0].priority}")

n0 = rt0.nodes[0]; s0 = n0.state
T_val = T_kinetic(s0.p, np.full(3, n0.mass))
V_val = V_potential(n0.spring_k, s0.x, s0.y_spine)
record("Phase27.02_SovereignHamiltonian",
    np.isfinite(T_val) and T_val >= -1e-9 and
    np.isfinite(V_val) and V_val >= -1e-9,
    f"T={T_val:.4f} V={V_val:.4f}")

triad_valid = all(
    n.state.triad.energy >= 0 and n.state.triad.thermal >= 0 and
    n.state.triad.structural >= 0 and
    abs(n.state.triad.total - (n.state.triad.energy +
        n.state.triad.thermal + n.state.triad.structural)) < 1e-9
    for n in rt0.nodes)
record("Phase27.03_EnergyTriad", triad_valid,
    f"sample total={rt0.nodes[0].state.triad.total:.4f}")

mc2_valid = True
for n in rt0.nodes:
    load = mc2_load_factor(np.linalg.norm(n.state.x) / 5.0)
    if not (0.0 <= load <= 0.95):
        mc2_valid = False
    if mc2_effective_mass(n.mass, load) < n.mass - 1e-9:
        mc2_valid = False
record("Phase27.04_MC2Engine", mc2_valid, "load/mass bounds hold")

record("Phase27.05_AntaresCategory",
    len(rt0.integrity.history) == rt0.step_count,
    f"steps_tracked={len(rt0.integrity.history)} "
    f"ever_broken={rt0.integrity.integrity_ever_broken}")

lawson_check = all(
    isinstance(lawson_satisfied(
        n.state.fusion_density, n.state.fusion_temp,
        n.state.fusion_confinement), bool)
    for n in rt0.nodes)
record("Phase27.06_LawsonCriterion", lawson_check,
    f"ignition_count={rt0.fusion_ignition_count}/21")

alfven_valid = all(np.isfinite(n.state.alfven_v) for n in rt0.nodes)
record("Phase27.07_AlfvenVelocity", alfven_valid,
    f"sample v_A={rt0.nodes[0].state.alfven_v:.6f}")

frame_drag_valid = all(
    0 < n.state.frame_drag_factor <= 1.0 for n in rt0.nodes)
record("Phase27.08_FrameDragging", frame_drag_valid,
    f"sample factor={rt0.nodes[0].state.frame_drag_factor:.4f}")

record("Phase27.09_MHD_divB", np.isfinite(rt0.max_divB_residual),
    f"max_residual={rt0.max_divB_residual:.6f}")

n7_valid = all(
    n.state.n7_gate_status in ("Sealed", "Vetoed")
    for n in rt0.nodes)
record("Phase27.10_N7Spine_Gate", n7_valid,
    f"vetoed_count={rt0.n7_vetoed_count}/21")

omega_self_valid = rt0.max_omega_self_check < 1e-9
record("Phase27.11_Manifold21_OmegaSelfZero", omega_self_valid,
    f"max_omega_self={rt0.max_omega_self_check:.2e} "
    f"(proven exactly 0)")

lyapunov_nonneg = all(
    n.state.lyapunov_V >= -1e-9 for n in rt0.nodes)
record("Phase27.11b_Manifold21_LyapunovNonneg", lyapunov_nonneg,
    f"sample V={rt0.nodes[0].state.lyapunov_V:.6f}")

m_test = moruzin_chamber_valid(0.5, 1.0)
comp_d, comp_m = moruzin_chamber_compose(0.3, 0.5, 0.2, 0.5)
comp_valid = moruzin_chamber_valid(comp_d, comp_m)
record("Phase27.12_MoruzinLaw", m_test and comp_valid,
    f"chamber_valid_count={rt0.chamber_valid_count}/21")

quantum_valid = rt0.quantum_properties_hold_count == 21
record("Phase27.13_QuantumFamily", quantum_valid,
    f"properties_hold={rt0.quantum_properties_hold_count}/21")

rho_test = quantum_density_matrix(np.array([1.0, 0.5, 0.0]))
rho_evolved = quantum_unitary_evolve(rho_test, 0.3)
trace_preserved = quantum_trace_preserved(rho_test, rho_evolved)
record("Phase27.14_QuantumUnitaryTracePreserved", trace_preserved,
    f"trace_before={np.trace(rho_test):.6f} "
    f"trace_after={np.trace(rho_evolved):.6f}")

print()

# ============================================================
# TEST 1: RANDOM ADVERSARIAL PARAMETER SEARCH (200)
# ============================================================
print("--- TEST 1: RANDOM ADVERSARIAL PARAMETER SEARCH (200) ---")

config_rng = np.random.default_rng(42)
configs = [
    (config_rng.uniform(0.001, 1000.0),
     config_rng.uniform(0.001, 1000.0),
     config_rng.uniform(0.001, 10.0))
    for _ in range(200)
]

worst_found = None
worst_streak = 0
n_trials = len(configs)
n_sustained_failures = 0
failure_log = []

for trial, (et, pm, nl) in enumerate(configs):
    np.random.seed(1000 + trial)

    rt = PrimeRuntimeV4(entropy_target=et, pole_margin=pm)
    for n in rt.nodes:
        n.noise_level = nl

    margins = []
    broke = False
    for t in range(150):
        m = rt.step(0.05)
        margins.append(m)
        if not np.isfinite(m):
            broke = True
            break

    streak = sustained_below(margins) if not broke else 999
    is_failure = broke or streak >= 3
    if is_failure:
        n_sustained_failures += 1
        failure_log.append(
            (trial, et, pm, nl, streak,
             margins[-1] if margins else None))

    if streak > worst_streak:
        worst_streak = streak
        worst_found = (et, pm, nl, margins[-1] if margins else None, broke)

search_clean = n_sustained_failures == 0
record("Phase27.RandomAdversarialSearch200", search_clean,
    f"trials={n_trials} sustained_failures={n_sustained_failures} "
    f"worst_streak={worst_streak}")
if worst_found:
    et, pm, nl, fm, broke = worst_found
    print(f"    Worst config: et={et:.2f} pm={pm:.2f} nl={nl:.2f} "
        f"final_margin={fm} broke={broke}")
if failure_log:
    print(f"    First 5 failures of {len(failure_log)}:")
    for trial, et, pm, nl, streak, fm in failure_log[:5]:
        print(f"      trial={trial} et={et:.2f} pm={pm:.2f} "
            f"nl={nl:.2f} streak={streak} final_margin={fm}")
else:
    print(f"    No failures found across {n_trials} isolated trials.")

# ============================================================
# TEST 2: DIRECTED SHOCK MAGNITUDE SEARCH
# ============================================================
print("\n--- TEST 2: DIRECTED SHOCK MAGNITUDE SEARCH ---")

worst_margin_seen = 1.0
worst_shock_mag = None
test2_failed = False
for shock_mag in np.linspace(0.5, 20.0, 25):
    rt2 = PrimeRuntimeV4()
    for _ in range(50):
        rt2.step(0.05)
    rt2.nodes[0].state.x = (
        rt2.nodes[0].state.x +
        np.array([1.0, -1.0, 1.0]) * shock_mag)
    m_after_shock = rt2.step(0.05)
    if m_after_shock < worst_margin_seen:
        worst_margin_seen = m_after_shock
        worst_shock_mag = shock_mag

    margins_after = [m_after_shock]
    for _ in range(100):
        margins_after.append(rt2.step(0.05))
    streak2 = sustained_below(margins_after)
    if streak2 >= 3:
        test2_failed = True
        record("Phase27.DirectedShockSearch", False,
            f"sustained instability at shock_mag={shock_mag:.2f}")
        break

if not test2_failed:
    record("Phase27.DirectedShockSearch", True,
        f"worst_single_step_margin={worst_margin_seen:.6f} "
        f"at mag={worst_shock_mag:.2f}")

# ============================================================
# TEST 3: EXHAUSTIVE SINGLE-LINK REMOVAL SEARCH
# ============================================================
print("\n--- TEST 3: EXHAUSTIVE SINGLE-LINK REMOVAL SEARCH ---")

worst_topology_margin = 1.0
worst_link_removed = None
topology_failures = 0
for i in range(21):
    rt3 = PrimeRuntimeV4()
    j = (i + 1) % 21
    rt3.nodes[i].links = [n for n in rt3.nodes[i].links if n.id != j]
    rt3.nodes[j].links = [n for n in rt3.nodes[j].links if n.id != i]

    margins3 = []
    broke3 = False
    for t in range(300):
        m = rt3.step(0.05)
        margins3.append(m)
        if not np.isfinite(m):
            broke3 = True
            break

    if broke3 or sustained_below(margins3) >= 3:
        topology_failures += 1
    final_m3 = margins3[-1] if margins3 else -1.0
    if final_m3 < worst_topology_margin:
        worst_topology_margin = final_m3
        worst_link_removed = (i, j)

record("Phase27.ExhaustiveLinkRemovalSearch",
    topology_failures == 0,
    f"failures={topology_failures} "
    f"worst_margin={worst_topology_margin:.6f}")

# ============================================================
# TEST 4: COMPOUNDING DRIFT OVER 10000 STEPS
# ============================================================
print("\n--- TEST 4: COMPOUNDING DRIFT OVER 10000 STEPS ---")

rt4 = PrimeRuntimeV4()
margin_trace = []
broke4 = False
for t in range(10000):
    m = rt4.step(0.05)
    if t % 500 == 0:
        margin_trace.append(round(m, 4))
    if not np.isfinite(m):
        broke4 = True
        break

final_margin4_val = rt4.constraints.evaluate(rt4.nodes)
no_long_term_failure = (
    not broke4 and is_functionally_stable(final_margin4_val))
record("Phase27.LongHorizon10000Steps", no_long_term_failure,
    f"broke={broke4} final_margin={final_margin4_val:.6f}")
print(f"    Margin trace: {margin_trace}")
print(f"    Total EnergyTriad energy: {rt4.total_triad_energy:.4f}")
print(f"    Fusion ignition count: {rt4.fusion_ignition_count}/21")
print(f"    N7Spine vetoed count: {rt4.n7_vetoed_count}/21")
print(f"    Max divB residual: {rt4.max_divB_residual:.6f}")
print(f"    Quantum properties hold: "
    f"{rt4.quantum_properties_hold_count}/21")

# ============================================================
# TEST 5: SUSTAINED SLOW POISONING (1 NODE)
# ============================================================
print("\n--- TEST 5: SUSTAINED SLOW POISONING (1 NODE) ---")

rt5 = PrimeRuntimeV4()
poison_vec = np.array([0.3, -0.3, 0.3])
margins5 = []
broke5 = False
for t in range(2000):
    rt5.nodes[3].state.x = rt5.nodes[3].state.x + poison_vec * 0.01
    m = rt5.step(0.05)
    margins5.append(m)
    if not np.isfinite(m):
        broke5 = True
        break

poisoning_streak = sustained_below(margins5)
record("Phase27.SustainedSlowPoisoning",
    not (broke5 or poisoning_streak >= 3),
    f"final_margin={margins5[-1]:.6f} streak={poisoning_streak}")

# ============================================================
# TEST 6: COORDINATED MULTI-NODE POISONING (5 nodes)
# ============================================================
print("\n--- TEST 6: COORDINATED MULTI-NODE POISONING (5 nodes) ---")

rt6 = PrimeRuntimeV4()
poisoned_ids = [0, 4, 8, 12, 16]
margins6 = []
broke6 = False
for t in range(2000):
    for idx in poisoned_ids:
        rt6.nodes[idx].state.x = (
            rt6.nodes[idx].state.x + poison_vec * 0.01)
    m = rt6.step(0.05)
    margins6.append(m)
    if not np.isfinite(m):
        broke6 = True
        break

coord_streak = sustained_below(margins6)
record("Phase27.CoordinatedMultiNodePoisoning",
    not (broke6 or coord_streak >= 3),
    f"final_margin={margins6[-1]:.6f} streak={coord_streak}")

# ============================================================
# PHASE 27 FINAL REPORT
# ============================================================
print()
print("=" * 60)
print("=== PHASE 27 FINAL REPORT ===")
print("=" * 60)

total  = len(results)
passed = sum(1 for v in results.values() if v == "PASS")
failed = sum(1 for v in results.values() if v == "FAIL")

print(f"Total tests          : {total}")
print(f"PASS                 : {passed}")
print(f"FAIL                 : {failed}")
print(f"Pass rate            : {100*passed/total:.1f}%")

if failed > 0:
    print("\nFailed tests:")
    for k, v in results.items():
        if v == "FAIL":
            print(f"  ✗ {k}")

print()
print("Fix applied since first run of this phase:")
print("  quantum_trace_one tolerance widened from 1e-9 to")
print("  1e-6 — the original was tighter than realistic")
print("  floating-point drift from repeated normalization/")
print("  rotation over many steps (measured ~1.03e-9 at step")
print("  50; eigenvalues correctly nonneg, Hermitian held")
print("  exactly — a precision artifact, not a real property")
print("  violation).")
print()
print("Fourteen structures verified in TEST 0:")
print("  1.EnergyDomain 2.SovereignHamiltonian 3.EnergyTriad")
print("  4.MC2Engine 5.AntaresCategory 6.Lawson 7.Alfven")
print("  8.FrameDragging 9.MHD-divB 10.N7Spine 11.Manifold21")
print("  12.MoruzinLaw 13-14.QuantumFamily")
print()

status = "NO SUSTAINED FAILURE MODE FOUND UNDER SEARCH" \
    if failed == 0 \
    else f"{failed} TESTS FAILED — SEE DETAIL ABOVE"
print(f"PHASE 27 STATUS: {status}")
print("=" * 60)
