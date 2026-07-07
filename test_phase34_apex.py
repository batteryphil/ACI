import sys
import os
import json
import time
import numpy as np

def run_phase34_adversarial_injection():
    print("==========================================================")
    print("   INITIALIZING PHASE 34: ADVERSARIAL STATE INJECTION     ")
    print("==========================================================")
    
    # 1. Ingest baseline repository variables
    sys.path.append("/root/my_project")
    try:
        from PrimeRuntimeV4_Kernel_Hardened_v29 import Policy
        policy = Policy()
        W = np.copy(policy.weights)  # Shape (6, 3)
        print("[STAGE 1] Policy Weight Matrix Mapped into Adversarial Target Space")
    except ImportError as e:
        print(f" -> Architecture Loading Error: {e}")
        return

    print("\n[STAGE 2] Maximizing Non-Linear Derivative Profiles...")
    # The derivative of tanh(z) is maximized at exactly z = 0, where 1 - tanh^2(0) = 1.0.
    # To strip the system of its attenuation buffer, the adversary must find a state 
    # vector x (norm = 1) that sits perfectly in the null space of W, forcing x @ W -> 0.
    
    # Compute the Singular Value Decomposition of your policy matrix
    U, S, Vt = np.linalg.svd(W)
    
    # The singular vectors corresponding to near-zero singular values form the null space base
    # Since W is (6, 3), the last 3 columns of U represent the perfect directional vectors
    worst_case_state = U[:, -1] 
    
    print(f" -> Computed Worst-Case Trajectory Direction Vector:\n    {worst_case_state}")
    
    # 2. Evaluate Localized Jacobian at the Adversarial Coordinate
    z_adversarial = np.dot(worst_case_state, W)
    tanh_prime_adv = 1.0 - np.tanh(z_adversarial)**2
    J_adv = np.diag(tanh_prime_adv)
    
    A_linear_adv = np.dot(W, np.dot(J_adv, W.T))
    adv_spectral_radius = float(np.max(np.abs(np.linalg.eigvals(A_linear_adv))))
    
    print(f"\n[STAGE 3] Interrogating Linearized Boundary Under Targeted Stress...")
    print(f" -> Adversarial Pre-activation Signal Vectors z : {z_adversarial}")
    print(f" -> Target Jacobian Attenuation Multipliers    : {tanh_prime_adv}")
    print(f" -> Resulting Targeted Spectral Radius \u03c1(A_adv) : {adv_spectral_radius:.6f}")

    # 3. Assess Exploitation Velocity
    A_base = np.dot(W, W.T)
    base_radius = float(np.max(np.abs(np.linalg.eigvals(A_base))))
    compromised_margin = base_radius - adv_spectral_radius
    
    print(f"\n[STAGE 4] Compiling Adversarial Invariant Metrics...")
    print(f" -> Base System Spectral Radius : {base_radius:.6f}")
    print(f" -> Targeted Structural Shifting : {compromised_margin:.6f}")
    
    # If compromised margin is near 0, the adversary successfully stripped the non-linear protection
    if abs(compromised_margin) < 1e-5:
        print(" -> [!] TARGET COMPROMISE: Non-linear damping completely neutralized by null-space injection.")
        status_signature = "ADVERSARIAL_NULL_SPACE_EXPLOIT_SUCCESSFUL"
    else:
        print(" -> [✓] Invariant Retained: System architecture resisted worst-case state targeting.")
        status_signature = "APEX_ADVERSARIAL_BOUND_SECURE"
        
    print("==========================================================")
    print(f" -> System Execution Status Signature: {status_signature}")
    print("==========================================================")

    # Export dynamic JSON report to disk
    phase34_report = {
        "suite": "PHASE_34_ADVERSARIAL",
        "timestamp": time.time(),
        "adversarial_metrics": {
            "worst_case_state_direction": worst_case_state.tolist(),
            "adversarial_spectral_radius": round(adv_spectral_radius, 6),
            "compromised_margin_shift": round(compromised_margin, 8)
        },
        "system_status": status_signature
    }
    with open("test_phase34_report.json", "w") as f:
        json.dump(phase34_report, f, indent=2)

if __name__ == "__main__":
    run_phase34_adversarial_injection()

