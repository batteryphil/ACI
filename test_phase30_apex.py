import sys
import numpy as np
sys.path.append("/root/my_project")

from PrimeRuntimeV4_Kernel_Hardened_v29 import EntropyEngine, State

def run_phase_30():
    print("--- Phase 30: Executing Corrected FSI Remediation Protocol ---")
    
    # 1. Setup Engine and State
    engine = EntropyEngine(target_entropy=0.1)
    state = State()
    state.x = np.array([2.0, 2.0, 2.0]) 
    trajectory = np.array([state.x, state.x * 2.5])
    
    initial_div = engine.calculate_divergence(trajectory)
    print(f"Initial Divergence: {initial_div}")
    
    # 2. Remediation Logic with Floating-Point Tolerance
    try:
        if initial_div > engine.target:
            print("Divergence breach detected. Executing formal remediation...")
            
            factor = np.sqrt(engine.target / initial_div)
            state.x *= factor
            
            new_trajectory = np.array([state.x, state.x * 2.5])
            final_div = engine.calculate_divergence(new_trajectory)
            
            print(f"Post-Remediation Divergence: {final_div}")
            
            # Use math.isclose or a small epsilon for tolerance
            if np.isclose(final_div, engine.target, atol=1e-9) or final_div < engine.target:
                print("PHASE 30 PASSED: Autonomous system integrity verified.")
            else:
                raise ValueError(f"Remediation target not met. Result: {final_div}")
        else:
            print("System within norms.")
            
    except Exception as e:
        print(f"PHASE 30 FAILED: {e}")
        sys.exit(1)

if __name__ == "__main__":
    run_phase_30()

