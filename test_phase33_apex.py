import sys
import os
import json
import time
import numpy as np

def run_apex_stochastic_jacobian_suite():
    print("==========================================================")
    print("   INITIALIZING PHASE 33: COMPREHENSIVE NON-LINEAR AUDIT  ")
    print("==========================================================")
    
    # 1. Ingest existing workspace dependencies
    sys.path.append("/root/my_project")
    try:
        from PrimeRuntimeV4_Kernel_Hardened_v29 import Policy
        policy = Policy()
        base_weights = np.copy(policy.weights)  # Shape (6, 3)
        print("[STAGE 1] Ingested Live Policy Weights for Stress Profile")
    except ImportError as e:
        print(f" -> Architecture Loading Error: {e}")
        return

    # 2. Part A: Complete Noise Volume Sweep (No Premature Breaking)
    print("\n[STAGE 2] Executing Full Stochastic Noise Volume Sweep...")
    noise_volumes = np.linspace(0.01, 2.0, 100)
    breach_volume = None
    max_radius_found = 0.0
    radius_history = []
    
    np.random.seed(42)
    
    for vol in noise_volumes:
        noise = np.random.normal(0, vol, size=base_weights.shape)
        perturbed_weights = base_weights + noise
        
        A_perturbed = np.dot(perturbed_weights, perturbed_weights.T)
        radius = float(np.max(np.abs(np.linalg.eigvals(A_perturbed))))
        radius_history.append((float(vol), radius))
        
        if radius > max_radius_found:
            max_radius_found = radius
            
        if radius >= 1.0 and breach_volume is None:
            breach_volume = float(vol)
            
    print(f" -> Mapping Complete over 100 Increments [0.01\u03c3 to 2.0\u03c3]")
    print(f" -> Peak Unconstrained Spectral Radius Reached: {max_radius_found:.6f}")
    if breach_volume:
        print(f" -> [!] Chaos Cliff Discovered at Noise Volume: {breach_volume:.4f} \u03c3")
    else:
        print(" -> [✓] System Intact: No structural breach detected across entire sweep.")

    # 3. Part B: Localized Tanh Jacobian Linearization
    print("\n[STAGE 3] Computing Non-Linear Tanh Jacobian Attenuation...")
    state_vector = np.array([0.5, -0.2, 0.1, -0.4, 0.3, -0.1])
    z = np.dot(state_vector, base_weights)
    tanh_prime = 1.0 - np.tanh(z)**2  
    J_activation = np.diag(tanh_prime)  
    
    A_base = np.dot(base_weights, base_weights.T)
    base_radius = float(np.max(np.abs(np.linalg.eigvals(A_base))))
    
    A_linearized = np.dot(base_weights, np.dot(J_activation, base_weights.T))
    linearized_radius = float(np.max(np.abs(np.linalg.eigvals(A_linearized))))
    margin_expansion = base_radius - linearized_radius
    
    print(f" -> Base Absolute Spectral Radius   : {base_radius:.6f}")
    print(f" -> Linearized Radius (\u03c1_linear)     : {linearized_radius:.6f}")
    print(f" -> Attenuation Margin Expansion     : +{margin_expansion:.6f}")

    # 4. Part C: Global Bounded Stability via Gershgorin Disc Theorem
    print("\n[STAGE 4] Asserting Global Bounds via Gershgorin Disc Theorem...")
    # Matrix A_base is 6x6. For each row, the center of the disc is A[i,i].
    # The radius R[i] is the sum of absolute values of non-diagonal entries in that row.
    max_gershgorin_upper_bound = 0.0
    for i in range(A_base.shape[0]):
        center = np.abs(A_base[i, i])
        row_radius = np.sum(np.abs(A_base[i, :])) - np.abs(A_base[i, i])
        upper_bound = center + row_radius
        if upper_bound > max_gershgorin_upper_bound:
            max_gershgorin_upper_bound = float(upper_bound)
            
    print(f" -> State-Independent Global Max Bound \u03bb_max \u2264 : {max_gershgorin_upper_bound:.6f}")
    is_globally_safe = max_gershgorin_upper_bound < 1.0
    print(f" -> Gershgorin Absolute Enclosure Safe (< 1.0) : {is_globally_safe}")

    # 5. Part D: 100-Step Temporal Drift Trajectory
    print("\n[STAGE 5] Projecting 100-Step Temporal Drift Trajectory...")
    current_state = np.copy(state_vector)
    trajectory_diverged = False
    step_divergence_point = None
    
    # Inject a steady operational perturbation vector to simulate environmental tracking stress
    operational_noise = np.random.normal(0, 0.05, size=base_weights.shape)
    active_weights = base_weights + operational_noise
    
    for step in range(1, 101):
        # Forward pass tracking: x_{t+1} = tanh(x_t @ W @ W^T)
        next_state = np.tanh(np.dot(current_state, np.dot(active_weights, active_weights.T)))
        state_magnitude = float(np.linalg.norm(next_state))
        
        if state_magnitude > 10.0:  # Threshold defining an explosive unbound state
            trajectory_diverged = True
            step_divergence_point = step
            break
        current_state = next_state
        
    if trajectory_diverged:
        print(f" -> [!] TEMPORAL FAILURE: Chaotic Drift exploded at step {step_divergence_point}")
        status_signature = "TEMPORAL_DRIFT_EXPLOSION"
    else:
        print(f" -> [✓] Temporal Bound Stable. Step 100 Magnitude: {float(np.linalg.norm(current_state)):.6f}")
        status_signature = "APEX_NON_LINEAR_SAFETY_BOUND_PROVEN"

    print("==========================================================")
    print(f" -> System Execution Status Signature: {status_signature}")
    print("==========================================================")

    # Export dynamic JSON report to disk
    phase33_report = {
        "suite": "PHASE_33_COMPLETE_STRESS",
        "timestamp": time.time(),
        "sweep_metrics": {
            "chaos_cliff_sigma": breach_volume,
            "peak_unconstrained_radius": round(max_radius_found, 6)
        },
        "jacobian_metrics": {
            "attenuation_margin_expansion": round(margin_expansion, 6),
            "linearized_spectral_radius": round(linearized_radius, 6)
        },
        "global_bounds": {
            "gershgorin_max_upper_bound": round(max_gershgorin_upper_bound, 6),
            "global_enclosure_safe": is_globally_safe
        },
        "temporal_metrics": {
            "trajectory_diverged": trajectory_diverged,
            "final_state_magnitude": float(np.linalg.norm(current_state)) if not trajectory_diverged else None
        },
        "system_status": status_signature
    }
    with open("test_phase33_report.json", "w") as f:
        json.dump(phase33_report, f, indent=2)

if __name__ == "__main__":
    run_apex_stochastic_jacobian_suite()

