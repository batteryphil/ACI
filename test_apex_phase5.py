import sys
import os
import json
import time
import numpy as np

sys.path.append("/root/my_project")

def run_tier5_apex_phase5_stress_matrix():
    print("==========================================================================")
    print("  INITIALIZING TIER 5 APEX PHASE 5: LAWSON CRITERION & ADVERSARIAL ATTACK ")
    print("==========================================================================")

    try:
        from VerifyBridge import VerifyBridge
        from lean_bounds import LeanBounds
        import PrimeRuntimeV4_backup as engine_mod

        bridge = VerifyBridge()
        results_data = bridge.read_lean_result()
        print(f"[INIT] Apex Matrix Connected. Synced with Formal Theorem Registry.")
    except ImportError as e:
        print(f" -> Architecture Connection Error: {e}")
        sys.exit(1)

    for idx, node in enumerate(bridge.rt.nodes):
        node.state.x = np.array([float(idx * 0.15), float(-idx * 0.08), 2.5], dtype=float)
        node.state.p = np.array([1.2, -0.5, float(idx * 0.04)], dtype=float)
        node.state.f = np.array([0.1, 0.1, -0.1], dtype=float)

    dt = 0.02
    simulation_telemetry = []
    node_count = len(bridge.rt.nodes)

    print("\n[PHASE 5 EXEC] Stepping Through 1500 Cycles under Unified Stress Vectors...")
    for step in range(1, 1501):

        if step >= 100 and step <= 400:
            for n in bridge.rt.nodes:
                n.noise_level = 0.85

        if step == 600:
            print("\n[!!!] ADVERSARIAL EVENT: Policy Loop targeting weakest Node...")
            margins = [float(n.state.local_margin) for n in bridge.rt.nodes]
            weakest_idx = int(np.argmin(margins))
            adv_node = bridge.rt.nodes[weakest_idx]
            adv_node.state.x = np.full(3, 1200.0, dtype=float)
            adv_node.state.f = np.full(3, 2500.0, dtype=float)

        if step == 1100:
            print("\n[!!!] LAWSON OVERLOAD: Spiking Plasma Confinement Fields...")
            for n in bridge.rt.nodes:
                n.state.fusion_density = 5e21
                n.state.fusion_temp = 15.0
                n.state.fusion_confinement = 2.0
                satisfied = engine_mod.lawson_satisfied(
                    n.state.fusion_density, n.state.fusion_temp, n.state.fusion_confinement)
                if satisfied:
                    n.state.local_margin *= 0.01

        margin_values = [float(n.state.local_margin) for n in bridge.rt.nodes]
        status_str, bottleneck_idx = engine_mod.n7_gate_decision(margin_values, floor=0.05)

        if status_str == "Vetoed" and bottleneck_idx is not None:
            isolated_node = bridge.rt.nodes[bottleneck_idx]
            if len(isolated_node.links) > 0:
                for neighbor in isolated_node.links:
                    if isolated_node in neighbor.links:
                        neighbor.links.remove(isolated_node)
                isolated_node.links = []

            damping_ratio = 0.85
            isolated_node.state.x *= (1.0 - damping_ratio)
            isolated_node.state.u *= (1.0 - damping_ratio)
            isolated_node.state.f *= (1.0 - damping_ratio)
            isolated_node.state.p *= (1.0 - damping_ratio)

            if float(np.linalg.norm(isolated_node.state.x)) < 1.0:
                isolated_node.state.x = np.zeros(3)
                isolated_node.state.u = np.zeros(3)
                isolated_node.state.f = np.zeros(3)
                isolated_node.state.p = np.zeros(3)

        for idx in range(node_count):
            n = bridge.rt.nodes[idx]
            if len(n.links) == 0 and float(np.linalg.norm(n.state.x)) == 0.0:
                prev_idx = (idx - 1) % node_count
                next_idx = (idx + 1) % node_count
                prev_node = bridge.rt.nodes[prev_idx]
                next_node = bridge.rt.nodes[next_idx]
                if n not in prev_node.links:
                    prev_node.links.append(n)
                if n not in next_node.links:
                    next_node.links.append(n)
                n.links = [prev_node, next_node]

        step_res = bridge.verified_step(dt)
        current_margin = float(step_res.get('margin', 0.0))

        if (step == 1 or step == 100 or step == 400 or step == 600 or
                step == 601 or step == 1100 or step == 1101 or step == 1500):
            print(f"  -> Cycle {step:04d}/1500 | Core System Margin Calculation: {current_margin:.6f} | STATUS: {step_res['status']}")

        step_metrics = {
            "iteration": step,
            "system_margin": current_margin,
            "node_telemetry_slices": []
        }
        for n in bridge.rt.nodes:
            step_metrics["node_telemetry_slices"].append({
                "node_id": n.id,
                "local_margin": float(n.state.local_margin),
                "lyapunov_V": float(n.state.lyapunov_V)
            })
        simulation_telemetry.append(step_metrics)

    print("\n[PHASE 5 EVAL] Checking Final Inter-Domain Gate Consensus Matrix...")
    inference_decision = bridge.rt.run_inference(bridge.rt.manifold_state)
    print(f" -> Consensus Engine Core Return Payload: {inference_decision}")

    total_lyapunov_pot = sum(float(n.state.lyapunov_V) for n in bridge.rt.nodes)
    total_leak_magnitude = sum(float(np.linalg.norm(n.state.mc2_leaked_delta)) for n in bridge.rt.nodes)
    final_verification_string = bridge.rt.verify_all()

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
        "verification_profile": final_verification_string,
        "evolution_history": simulation_telemetry
    }

    with open("production_intelligence_metrics.json", "w") as f:
        json.dump(apex_intelligence_report, f, indent=2)
    print("\n==========================================================================")
    print(" -> DATA ARCHIVE EXPORT SUCCESSFUL: Saved to production_intelligence_metrics.json")
    print("==========================================================================")

if __name__ == "__main__":
    run_tier5_apex_phase5_stress_matrix()
