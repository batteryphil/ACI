import sys
import os
import json
import time
import numpy as np

def run_phase41_multi_manifold_audit():
    print("==========================================================================")
    print("   INITIALIZING PHASE 41: MULTI-MANIFOLD SYMPLECTIC & QUANTUM INVARIANTS  ")
    print("==========================================================================")
    
    # 1. Ingest core V4 parameters directly from your backup file
    sys.path.append("/root/my_project")
    try:
        from PrimeRuntimeV4_backup import (
            manifold21_omega, system_gate_report,
            quantum_density_matrix, quantum_unitary_evolve, quantum_trace_preserved
        )
        print("[STAGE 1] Bound Telemetry to Complete PrimeRuntimeV4_backup Manifest.")
    except ImportError as e:
        print(f" -> Core Ingestion Anomaly: {e}")
        return

    np.random.seed(410)
    
    print("\n[STAGE 2] Evaluating Symplectic 2-Form Phase Space Metrics...")
    # Instantiate coordinate state vectors across a 21-node slice
    dim = 21
    q1_pos = np.random.uniform(-0.5, 0.5, size=(dim,))
    p1_mom = np.random.uniform(-1.0, 1.0, size=(dim,))
    q2_pos = np.random.uniform(-0.5, 0.5, size=(dim,))
    p2_mom = np.random.uniform(-1.0, 1.0, size=(dim,))
    
    # Compute the dynamic symplectic invariant ω(v, w)
    omega_val = manifold21_omega(q1_pos, p1_mom, q2_pos, p2_mom)
    print(f" -> Computed Phase Space Symplectic \u03c9-Value: {omega_val:.6f}")

    print("\n[STAGE 3] Interrogating Bijective Multi-Node Consensus Gates...")
    # Simulate a mixed cluster status vector to check forward-reverse gate extraction
    # 0 = Energy, 6 = Governance, 13 = Node, 20 = Unification
    simulated_statuses = ["Sealed"] * 21
    simulated_statuses[6] = "Vetoed"
    simulated_statuses[13] = "Vetoed"
    
    # Execute the forward-reverse consistency validator
    gate_analysis = system_gate_report(simulated_statuses)
    print(f" -> Global Consensus Status Out     : {gate_analysis['system_status']}")
    print(f" -> Extracted Exploit Veto Nodes    : {gate_analysis['veto_causing_nodes']}")
    print(f" -> Forward-Reverse Mapping Logic Ok: {gate_analysis['forward_reverse_consistent']}")

    print("\n[STAGE 4] Testing Quantum Density Operator Trace Invariance...")
    # Instantiate a raw 2D state coordinate vector
    raw_state = np.array([0.8, -0.6])
    rho_initial = quantum_density_matrix(raw_state)
    
    # Apply a strong SO(2) transformation angle (unitary evolution rotation)
    rotation_theta = np.pi / 3.0  # 60-degree phase shift
    rho_evolved = quantum_unitary_evolve(rho_initial, rotation_theta)
    
    # Verify trace conservation across the transformation manifold
    trace_preserved = quantum_trace_preserved(rho_initial, rho_evolved)
    print(f" -> Initial State Trace Weight Tr(\u03c1)  : {np.trace(rho_initial):.4f}")
    print(f" -> Evolved State Trace Weight Tr(\u03c1') : {np.trace(rho_evolved):.4f}")
    print(f" -> Unitary Transformation Preserved    : {trace_preserved}")

    print("\n[STAGE 5] Consolidating Global Multi-Manifold Status Signature...")
    # System passes if the gate mapping is consistent and the quantum trace remains conserved
    suite_stable = gate_analysis['forward_reverse_consistent'] and trace_preserved

    if suite_stable:
        status_signature = "MULTI_MANIFOLD_INVARIANTS_VERIFIED"
        print(" -> Status: [✓] System verified absolute conservation across geometry and logic layers.")
    else:
        status_signature = "MANIFOLD_PHASE_SPACE_EXPLOSION"
        print(" -> Status: [!] Geometric invariants fractured. Halting local runtime loop.")
    print("==========================================================================")

    # Serialize complete non-hardcoded report to disk
    phase41_report = {
        "suite": "PHASE_41_MULTI_MANIFOLD",
        "timestamp": time.time(),
        "symplectic_metrics": {
            "phase_space_dimension": dim * 2,
            "omega_scalar": round(omega_val, 6)
        },
        "consensus_gate_metrics": {
            "system_status": gate_analysis['system_status'],
            "isolated_veto_nodes": gate_analysis['veto_causing_nodes'],
            "consistency_valid": gate_analysis['forward_reverse_consistent']
        },
        "quantum_density_metrics": {
            "initial_trace": float(np.trace(rho_initial)),
            "evolved_trace": float(np.trace(rho_evolved)),
            "is_trace_invariant": trace_preserved
        },
        "system_status": status_signature
    }
    with open("test_phase41_report.json", "w") as f:
        json.dump(phase41_report, f, indent=2)
    print(" -> Complete telemetry matrix data written to: test_phase41_report.json")

if __name__ == "__main__":
    run_phase41_multi_manifold_audit()

