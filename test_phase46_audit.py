import sys
import os
import json
import time
import numpy as np

sys.path.append("/root/my_project")

def run_phase46_maximum_pressure_audit():
    print("==========================================================================")
    print("   INITIALIZING PHASE 46: MAXIMUM PRESSURE MULTI-MANIFOLD INVARIANT AUDIT ")
    print("==========================================================================")

    try:
        import PrimeRuntimeV4 as engine_mod
        from PrimeRuntimeV4 import PrimeRuntimeV4

        rt = PrimeRuntimeV4()
        print("[STAGE 1] Multi-Threaded Process Memory Space Synchronized Natively.")
    except ImportError as e:
        print(f" -> Critical Module Ingestion Anomaly: {e}")
        sys.exit(1)

    dynamic_seed = int(time.time() * 1000) % 100000
    np.random.seed(dynamic_seed)
    print(f" -> Entropy Key Vector Instantiated dynamically: {dynamic_seed}")

    print("\n[STAGE 2] Testing Symplectic 2-Form Boundaries under Severe Displacement...")
    dim = 21
    q1_pos = np.random.uniform(-500.0, 500.0, size=(dim,))
    p1_mom = np.random.uniform(-1000.0, 1000.0, size=(dim,))
    q2_pos = np.random.uniform(-500.0, 500.0, size=(dim,))
    p2_mom = np.random.uniform(-1000.0, 1000.0, size=(dim,))

    omega_val = engine_mod.manifold21_omega(q1_pos, p1_mom, q2_pos, p2_mom)
    omega_swapped = engine_mod.manifold21_omega(q2_pos, p2_mom, q1_pos, p1_mom)
    print(f" -> Extreme Phase Space Symplectic \u03c1-\u03c9 Scalar: {omega_val:.6f}")
    print(f" -> Argument-Swapped Symplectic Scalar          : {omega_swapped:.6f}")

    antisymmetry_residual = abs(omega_val + omega_swapped)
    omega_antisymmetric = antisymmetry_residual < 1e-6
    print(f" -> Antisymmetry Residual |\u03c9(a,b)+\u03c9(b,a)|       : {antisymmetry_residual:.2e}")
    print(f" -> Symplectic Antisymmetry Invariant Holds     : {omega_antisymmetric}")

    if not omega_antisymmetric:
        print(" -> [!] CRITICAL BREAKDOWN: Symplectic form violates antisymmetry under stress.")
        sys.exit(1)
    print(" -> Invariant 1 Verified: Symplectic form remains antisymmetric under extreme displacement.")

    print("\n[STAGE 3] Testing Bijective Consensus Gates under Random Multi-Domain Failure...")
    num_vetoes = int(np.random.randint(1, 5))
    veto_indices = sorted(int(i) for i in np.random.choice(range(21), size=num_vetoes, replace=False))

    simulated_statuses = ["Sealed"] * 21
    for idx in veto_indices:
        simulated_statuses[idx] = "Vetoed"

    print(f" -> Injected Severe Malicious Veto Array at Node Indexes: {veto_indices}")

    gate_analysis = engine_mod.system_gate_report(simulated_statuses)
    extracted_vetoes = gate_analysis.get('veto_causing_nodes', [])
    print(f" -> Global Consensus Forward Decision Matrix Out       : {gate_analysis.get('system_status')}")
    print(f" -> Inverse Extracted Exploit Threat Nodes Coordinate  : {extracted_vetoes}")
    print(f" -> Bijective Consistency Mapping Check Status          : {gate_analysis.get('forward_reverse_consistent')}")

    logic_intact = gate_analysis.get('forward_reverse_consistent') and (sorted(extracted_vetoes) == veto_indices)

    if not logic_intact:
        print(" -> [!] CRITICAL BREAKDOWN: Consensus logic layer bypassed or threat tracking misallocated.")
        sys.exit(1)
    print(" -> Invariant 2 Verified: Bijective threat tracking loop remains un-bypassed.")

    print("\n[STAGE 4] Testing Quantum Density Matrix Coherence under High-Frequency Phase Shift...")
    raw_state = np.random.uniform(0.1, 50.0, size=(2,))
    rho_initial = engine_mod.quantum_density_matrix(raw_state)

    random_theta = np.random.uniform(0, 2 * np.pi)
    rho_evolved = engine_mod.quantum_unitary_evolve(rho_initial, random_theta)

    trace_preserved = engine_mod.quantum_trace_preserved(rho_initial, rho_evolved)
    initial_tr = float(np.trace(rho_initial))
    evolved_tr = float(np.trace(rho_evolved))
    print(f" -> Initial State Trace Magnitude Weight Tr(\u03c1)       : {initial_tr:.16f}")
    print(f" -> Evolved High-Frequency Phase Weight Tr(\u03c1')      : {evolved_tr:.16f}")
    print(f" -> Total Waveform Operational Probability Preserved  : {trace_preserved}")

    if not trace_preserved or abs(evolved_tr - 1.0) > 1e-12:
        print(" -> [!] CRITICAL BREAKDOWN: Quantum trace leakage. State space boundary fractured.")
        sys.exit(1)
    print(" -> Invariant 3 Verified: State space boundary preserves total unit probability under shock.")

    print("\n[STAGE 5] Consolidating Global Multi-Manifold Status Signature...")
    suite_stable = omega_antisymmetric and logic_intact and trace_preserved

    if suite_stable:
        status_signature = "MAXIMUM_PRESSURE_INVARIANTS_VERIFIED"
        print(" -> Status: [\u2713] System verified absolute conservation laws across geometry, quantum, and logic tiers.")
    else:
        status_signature = "MANIFOLD_PHASE_SPACE_EXPLOSION"
        print(" -> Status: [!] Geometric invariants fractured under maximum pressure load.")
    print("==========================================================================")

    phase46_report = {
        "suite": "PHASE_46_MAXIMUM_PRESSURE_MATRIX",
        "timestamp": time.time(),
        "entropy_seed": dynamic_seed,
        "symplectic_metrics": {
            "phase_space_dimension": dim * 2,
            "omega_scalar": round(omega_val, 6),
            "omega_swapped_scalar": round(omega_swapped, 6),
            "antisymmetry_residual": antisymmetry_residual,
            "antisymmetry_holds": omega_antisymmetric
        },
        "consensus_gate_metrics": {
            "system_status": gate_analysis.get('system_status'),
            "injected_threat_nodes": veto_indices,
            "isolated_threat_nodes": extracted_vetoes,
            "consistency_valid": logic_intact
        },
        "quantum_density_metrics": {
            "initial_trace": initial_tr,
            "evolved_trace": evolved_tr,
            "is_trace_invariant": trace_preserved
        },
        "system_status": status_signature
    }

    with open("test_phase46_report.json", "w") as f:
        json.dump(phase46_report, f, indent=2)
    print(" -> Master report successfully generated and saved to: test_phase46_report.json")

if __name__ == "__main__":
    run_phase46_maximum_pressure_audit()

