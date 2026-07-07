import sys
import os
import json
import time
import numpy as np

sys.path.append("/root/my_project")

def run_apex_master_stress_harness():
    print("==========================================================================")
    print("  INITIALIZING TIER 5 APEX PHASE 3: CONCURRENT DEGRADATION & RE-STITCH    ")
    print("==========================================================================")

    try:
        import PrimeRuntimeV4_backup as engine_mod
        from PrimeRuntimeV4_backup import PrimeRuntimeV4, n7_M_N7, n7_gate_decision
        
        rt = PrimeRuntimeV4(node_count=21)
        print(f"[INIT] Phase 3 Matrix Engaged. Baseline Manifest: {rt.manifold_state}")
    except ImportError as e:
        print(f" -> Critical Unification Import Fault: {e}")
        sys.exit(1)

    print("\n[PHASE 3 INIT] Configuring Initial Spatial Coordinates across 21 Domains...")
    for idx, node in enumerate(rt.nodes):
        node.state.x = np.array([float(idx * 0.15), float(-idx * 0.08), 2.5], dtype=float)
        node.state.p = np.array([1.2, -0.5, float(idx * 0.04)], dtype=float)
        node.state.f = np.array([0.1, 0.1, -0.1], dtype=float)
        node.state.B_x = float(np.sin(idx))
        node.state.B_y = float(np.cos(idx))
        node.state.prev_B_x = float(np.sin(idx - 0.1))
        node.state.prev_B_y = float(np.cos(idx - 0.1))

    dt = 0.02
    simulation_telemetry = []
    checkpoint_steps = [1, 2, 3, 300, 301, 305, 500, 800, 801, 805, 1000, 1500]

    print("\n[PHASE 3 EXEC] Executing Advanced Invariant Stress-Recovery Loop (1500 Cycles)...")
    for step in range(1, 1501):
        
        # 1. Single Shock Event (Retained profile)
        if step == 300:
            print("\n[!!!] SINGLE SHOCK EVENT: Injecting Primary Disruption Vector into Node...")
            target_node = rt.nodes[0]
            target_node.state.x = np.full(3, 1000.0, dtype=float)
            target_node.state.u = np.full(3, 500.0, dtype=float)
            target_node.state.f = np.full(3, 2000.0, dtype=float)

        # 2. Distributed Concurrent Explosion Matrix (Multi-point failure indices)
        if step == 800:
            print("\n[!!!] MATRIX SHOCK EVENT: Injecting Concurrent Disruptions into Nodes...")
            trigger_list = [3, 7, 14, 19]
            for trigger_idx in trigger_list:
                target_node = rt.nodes[trigger_idx]
                target_node.state.x = np.full(3, 750.0, dtype=float)
                target_node.state.u = np.full(3, 350.0, dtype=float)
                target_node.state.f = np.full(3, 1500.0, dtype=float)

        # 3. Autonomous Mitigation, Severance, and Friction Damping
        if step >= 1:
            margin_values = [float(n.state.local_margin) for n in rt.nodes]
            status_str, bottleneck_idx = n7_gate_decision(margin_values, floor=0.05)

            if status_str == "Vetoed" and bottleneck_idx is not None:
                isolated_node = rt.nodes[bottleneck_idx]
                
                # Dynamic Topology Severance
                if len(isolated_node.links) > 0:
                    for neighbor in isolated_node.links:
                        if isolated_node in neighbor.links:
                            neighbor.links.remove(isolated_node)
                    isolated_node.links = []
                
                # Dynamic Heavy Damping Recovery Function
                damping_ratio = 0.85
                isolated_node.state.x *= (1.0 - damping_ratio)
                isolated_node.state.u *= (1.0 - damping_ratio)
                isolated_node.state.f *= (1.0 - damping_ratio)
                isolated_node.state.p *= (1.0 - damping_ratio)

                # Automated Fallback Recovery Routine
                if float(np.linalg.norm(isolated_node.state.x)) < 1.0:
                    isolated_node.state.x = np.zeros(3)
                    isolated_node.state.u = np.zeros(3)
                    isolated_node.state.f = np.zeros(3)
                    isolated_node.state.p = np.zeros(3)

        # 4. Automated Re-stitching Protocol
        if step >= 1:
            for idx in range(rt.node_count):
                n = rt.nodes[idx]
                if len(n.links) == 0 and float(np.linalg.norm(n.state.x)) == 0.0:
                    prev_idx = (idx - 1) % rt.node_count
                    next_idx = (idx + 1) % rt.node_count
                    prev_node = rt.nodes[prev_idx]
                    next_node = rt.nodes[next_idx]
                    
                    if n not in prev_node.links:
                        prev_node.links.append(n)
                    if n not in next_node.links:
                        next_node.links.append(n)
                    n.links = [prev_node, next_node]

        # 5. Process state evolution step
        current_margin = rt.step(dt=dt)
        
        # Real-time console outputs at boundary checkpoints
        if step in checkpoint_steps:
            print(f"  -> Cycle {step:04d}/1500 | Core System Margin Calculation: {current_margin:.6f}")

        step_metrics = {
            "iteration": step,
            "system_margin": current_margin,
            "node_telemetry_slices": []
        }

        for n in rt.nodes:
            step_metrics["node_telemetry_slices"].append({
                "node_id": n.id,
                "hamiltonian": float(n.state.hamiltonian),
                "local_margin": float(n.state.local_margin),
                "load_factor": float(n.state.load),
                "lyapunov_V": float(n.state.lyapunov_V)
            })
        simulation_telemetry.append(step_metrics)

    print("\n[PHASE 3 EVAL] Evaluating Final Inter-Domain Gate Consensus Matrix...")
    inference_decision = rt.run_inference(rt.manifold_state)
    print(f" -> Consensus Engine Core Return Payload: {inference_decision}")

    print("\n[PHASE 3 DIAG] Extracting Synaptic Policy Weight Spatial Variance Matrix...")
    weight_variances = []
    for n in rt.nodes:
        weight_variances.append(float(np.var(n.policy.weights)))
    print(f" -> Synaptic Weight Spatial Variances Profile: [Min: {min(weight_variances):.6f}, Max: {max(weight_variances):.6f}]")

    print("\n[PHASE 3 AUDIT] Auditing Active Production Conservation Invariants...")
    total_lyapunov_pot = sum(float(n.state.lyapunov_V) for n in rt.nodes)
    total_leak_magnitude = sum(float(np.linalg.norm(n.state.mc2_leaked_delta)) for n in rt.nodes)
    final_verification_string = rt.verify_all()

    print(f" -> Aggregate Lyapunov Parameter  : {total_lyapunov_pot:.6f}")
    print(f" -> Cumulative Network Leakage    : {total_leak_magnitude:.6f}")
    print(f" -> Final State Profile Summary   : {final_verification_string}")

    apex_intelligence_report = {
        "timestamp": time.time(),
        "inference_output": inference_decision,
        "conservation_metrics": {
            "aggregate_lyapunov_potential": total_lyapunov_pot,
            "total_mc2_cascade_leakage": total_leak_magnitude
        },
        "synaptic_policy_profile": weight_variances,
        "verification_profile": final_verification_string,
        "evolution_history": simulation_telemetry
    }

    with open("production_intelligence_metrics.json", "w") as f:
        json.dump(apex_intelligence_report, f, indent=2)
    print("\n==========================================================================")
    print(" -> DATA ARCHIVE EXPORT SUCCESSFUL: Saved to production_intelligence_metrics.json")
    print("==========================================================================")

if __name__ == "__main__":
    run_apex_master_stress_harness()

