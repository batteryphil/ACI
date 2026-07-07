import sys
import os
import json
import time
import numpy as np

def run_phase35_latency_stress():
    print("==========================================================")
    print("   INITIALIZING PHASE 35: NON-MARKOVIAN FEEDBACK LATENCY ")
    print("==========================================================")
    
    # 1. Ingest baseline repository parameters
    sys.path.append("/root/my_project")
    try:
        from PrimeRuntimeV4_Kernel_Hardened_v29 import Policy
        policy = Policy()
        W = np.copy(policy.weights)  # Shape (6, 3)
        A_base = np.dot(W, W.T)      # Shape (6, 6)
        print("[STAGE 1] Ingested System Transition Matrices for Temporal Audit")
    except ImportError as e:
        print(f" -> Architecture Loading Error: {e}")
        return

    print("\n[STAGE 2] Profiling Asynchronous Delay Trajectories...")
    # Simulate a history buffer over discrete frames
    # Max latency step to evaluate is k = 12 frames
    max_lag = 12
    coupling_alpha = 0.7  # State feedback gain coefficient
    
    # Track the variance at step 100 for each discrete delay factor
    delay_results = {}
    oscillation_detected = False
    critical_lag_threshold = None
    
    np.random.seed(101)
    
    for k in range(1, max_lag + 1):
        # Initialize a historical state ring buffer of size (k + 1)
        # Each entry is a 6-dimensional state vector
        history_buffer = [np.random.uniform(-0.5, 0.5, size=(6,)) for _ in range(k + 1)]
        
        trajectory_magnitudes = []
        
        # Run forward projection loop over 100 iterations
        for step in range(100):
            current_state = history_buffer[-1]
            delayed_state = history_buffer[0]  # Extract frame x_{t-k}
            
            # Non-Markovian feedback law calculation:
            next_state = (1.0 - coupling_alpha) * current_state + coupling_alpha * np.tanh(np.dot(delayed_state, A_base))
            
            # Update history ring buffer: pop oldest frame, append newest state
            history_buffer.pop(0)
            history_buffer.append(next_state)
            
            trajectory_magnitudes.append(float(np.linalg.norm(next_state)))
            
        # Analyze the final 20 steps for residual cyclical tracking variance (oscillations)
        tail_variance = float(np.var(trajectory_magnitudes[-20:]))
        delay_results[f"lag_k_{k}"] = tail_variance
        
        # If variance spikes or remains non-zero, it indicates an unresolved tracking cycle
        # A variance threshold of > 1e-4 identifies an active state oscillation
        if tail_variance > 1e-4 and not oscillation_detected:
            oscillation_detected = True
            critical_lag_threshold = k
            
    print(f" -> Completed Temporal Profiling up to Frame Lag Limit k = {max_lag}")
    for lag, val in delay_results.items():
        print(f"    [*] Feedback Delay Step {lag:10s} -> Tail Variance: {val:.12f}")

    print("\n[STAGE 3] Evaluating Asynchronous Stability Margins...")
    if oscillation_detected:
        print(f" -> [!] LATENCY BREAKDOWN: Cyclic feedback oscillations verified at lag k = {critical_lag_threshold}")
        status_signature = "NON_MARKOVIAN_OSCILLATION_DETECTED"
        directive = "RESTRUCTURE COUPLING LAYER GAIN INTO DELAY-COMPENSATED MATRIX."
    else:
        print(" -> [✓] Temporal Bound Secure: System mapping dampens out asynchronous latency drops.")
        status_signature = "APEX_TEMPORAL_LATENCY_BOUND_SECURE"
        directive = "CONTINUE EXECUTION. ASYNCHRONOUS TIMING CORRALS ARE CONVERGING."

    print("==========================================================")
    print(f" -> System Execution Status Signature: {status_signature}")
    print("==========================================================")

    # Export dynamic JSON report to disk
    phase35_report = {
        "suite": "PHASE_35_LATENCY",
        "timestamp": time.time(),
        "latency_metrics": {
            "max_evaluated_lag": max_lag,
            "coupling_gain_alpha": coupling_alpha,
            "critical_lag_threshold": critical_lag_threshold,
            "delay_variance_map": delay_results
        },
        "system_status": status_signature
    }
    with open("test_phase35_report.json", "w") as f:
        json.dump(phase35_report, f, indent=2)
    print(" -> Latency telemetry report written to: test_phase35_report.json")

if __name__ == "__main__":
    run_phase35_latency_stress()

