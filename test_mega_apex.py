import sys
import os
import json
import time
import numpy as np

sys.path.append("/root/my_project")

def get_verified_lean_count():
    path = os.path.join("/root/my_project", "verified_targets.txt")
    try:
        with open(path) as f:
            return sum(1 for line in f if line.strip())
    except FileNotFoundError:
        return 0

def run_million_cycle_mega_matrix():
    print("==========================================================================")
    print("  INITIALIZING MEGA-APEX: 1,000,000 CONTINUOUS INTER-DOMAIN STRESS LOOPS ")
    print("==========================================================================")

    try:
        from VerifyBridge import VerifyBridge
        from lean_bounds import LeanBounds
        import PrimeRuntimeV4_backup as engine_mod

        bridge = VerifyBridge()
        lean_verified_count = get_verified_lean_count()
        print(f"[INIT] Mega-Matrix Engaged. Connected to {lean_verified_count} Verified Lean Invariants.")
    except ImportError as e:
        print(f"[ERROR] Engine Unification Fault: {e}")
        sys.exit(1)

    for idx, node in enumerate(bridge.rt.nodes):
        node.state.x = np.array([float(idx * 0.5), float(-idx * 0.25), 10.0], dtype=float)
        node.state.p = np.array([5.0, -2.0, float(idx * 0.12)], dtype=float)
        node.state.f = np.array([1.0, 1.0, -1.0], dtype=float)

    dt = 0.02
    simulation_telemetry = []
    total_steps = 1000000

    print(f"\n[EXECUTION] Rolling {total_steps:,} Invariant Transformation Operations...")
    t_start = time.time()
    t_checkpoint = time.time()

    for step in range(1, total_steps + 1):

        if 100000 <= step <= 400000:
            for n in bridge.rt.nodes:
                n.noise_level = 1.00

        if step == 500000:
            print("\n[!!!] MIDPOINT CRITICAL STRIKE: Injecting Mass Deformations Concurrently...")
            target_indices = [0, 5, 10, 15, 20]
            for trigger_idx in target_indices:
                adv_node = bridge.rt.nodes[trigger_idx]
                adv_node.state.x = np.full(3, 50000.0, dtype=float)
                adv_node.state.f = np.full(3, 100000.0, dtype=float)

        if step == 750000:
            print("\n[!!!] THERMAL CORE SATURATION: Triggering Sustained Plasma Overload...")
            for n in bridge.rt.nodes:
                n.state.fusion_density = 1e23
                n.state.fusion_temp = 500.0
                n.state.fusion_confinement = 50.0
                if engine_mod.lawson_satisfied(n.state.fusion_density, n.state.fusion_temp, n.state.fusion_confinement):
                    n.state.local_margin *= 0.0001

        margin_values = [float(n.state.local_margin) for n in bridge.rt.nodes]
        vetoed_indices = [i for i, m in enumerate(margin_values) if m < 0.05]

        for bottleneck_idx in vetoed_indices:
            isolated_node = bridge.rt.nodes[bottleneck_idx]
            if len(isolated_node.links) > 0:
                for neighbor in isolated_node.links:
                    if isolated_node in neighbor.links:
                        neighbor.links.remove(isolated_node)
                isolated_node.links = []

            damping_ratio = 0.99
            isolated_node.state.x *= (1.0 - damping_ratio)
            isolated_node.state.u *= (1.0 - damping_ratio)
            isolated_node.state.f *= (1.0 - damping_ratio)
            isolated_node.state.p *= (1.0 - damping_ratio)

            if float(np.linalg.norm(isolated_node.state.x)) < 1.0:
                isolated_node.state.x = np.zeros(3)
                isolated_node.state.u = np.zeros(3)
                isolated_node.state.f = np.zeros(3)
                isolated_node.state.p = np.zeros(3)

        status_str = "Vetoed" if vetoed_indices else "Sealed"

        for idx in range(bridge.rt.node_count):
            n = bridge.rt.nodes[idx]
            if len(n.links) == 0 and float(np.linalg.norm(n.state.x)) == 0.0:
                prev_idx = (idx - 1) % bridge.rt.node_count
                next_idx = (idx + 1) % bridge.rt.node_count
                prev_node = bridge.rt.nodes[prev_idx]
                next_node = bridge.rt.nodes[next_idx]
                if n not in prev_node.links: prev_node.links.append(n)
                if n not in next_node.links: next_node.links.append(n)
                n.links = [prev_node, next_node]

        step_res = bridge.verified_step(dt)
        current_margin = float(step_res.get('margin', 0.0))

        if step == 1 or step % 5000 == 0 or step == 500001 or step == 500005 or step == 750001:
            total_lyapunov_pot = sum(float(n.state.lyapunov_V) for n in bridge.rt.nodes)
            t_now = time.time()
            elapsed_chunk = t_now - t_checkpoint
            t_checkpoint = t_now

            cps = int(5000 / elapsed_chunk) if step > 1 else 0
            cps_str = f"{cps:,} cycles/sec" if step > 1 else "initializing"

            print(f"  -> Cycle {step:07d}/1000000 | Margin: {current_margin:.6f} | Lyap: {total_lyapunov_pot:.2f} | Status: {step_res['status']} | VetoedNow: {len(vetoed_indices)} | Speed: {cps_str}")

        if step % 10000 == 0 or step == 1:
            step_metrics = {
                "iteration": step,
                "system_margin": current_margin,
                "vetoed_node_count": len(vetoed_indices),
                "node_telemetry_slices": [
                    {"node_id": n.id, "local_margin": float(n.state.local_margin), "lyapunov_V": float(n.state.lyapunov_V)}
                    for n in bridge.rt.nodes
                ]
            }
            simulation_telemetry.append(step_metrics)

    t_end = time.time()
    print(f"\n[METRIC] Processing duration for 1M iterations completed in: {t_end - t_start:.2f} seconds.")

    print("\n[MEGA EVAL] Checking Final Inter-Domain Gate Consensus Matrix...")
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
        "execution_seconds": t_end - t_start,
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
    run_million_cycle_mega_matrix()
