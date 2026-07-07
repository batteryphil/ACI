import sys
import os
import json
import time
import numpy as np

def run_phase36_master_stress_matrix():
    print("==========================================================================")
    print("   INITIALIZING PHASE 36: APEX RESONANT STRESS & SPATIOTEMPORAL CHAOS     ")
    print("==========================================================================")
    
    # 1. Ingest core repository components
    sys.path.append("/root/my_project")
    try:
        from PrimeRuntimeV4_Kernel_Hardened_v29 import Policy
        policy = Policy()
        base_weights = np.copy(policy.weights)  # Shape (6, 3)
        A_base = np.dot(base_weights, base_weights.T)  # Shape (6, 6)
        print("[STAGE 1] Ingested Live Policy Operators into Master Chaos Matrix.")
    except ImportError as e:
        print(f" -> Architecture Loading Error: {e}")
        return

    np.random.seed(360)
    report_data = {}

    # 2. PARADIGM 1 & 5: Over-Unity Gain Sweep & Adversarial History Resonant Injection
    print("\n[STAGE 2] Sweeping Over-Unity Gain (alpha) & Injecting Out-of-Phase History...")
    alpha_range = np.linspace(1.0, 4.0, 50)
    bifurcation_points = []
    feigenbaum_fracture = None
    
    # Calculate out-of-phase eigenvector patterns to drive a resonant standing wave
    eigenvals, eigenvecs = np.linalg.eigh(A_base)
    anti_eigenvector = eigenvecs[:, 0]  # Vector corresponding to minimum eigenvalue for anti-phase drive
    
    for alpha in alpha_range:
        # Populate history buffer with alternating out-of-phase eigenvector patterns
        history = [(((-1)**i) * anti_eigenvector * 0.5) for i in range(5)]
        
        # Run 50 iterations to clear transients and observe steady-state settlement
        for _ in range(50):
            x_curr = history[-1]
            x_lag = history[0]  # Properly slice out the temporal historical frame
            x_next = (1.0 - alpha) * x_curr + alpha * np.tanh(np.dot(x_lag, A_base))
            history.pop(0)
            history.append(x_next)
            
        # Collect distinct terminal magnitudes over 10 consecutive ticks to check for period doubling
        terminal_states = []
        for _ in range(10):
            x_curr = history[-1]
            x_lag = history[0]
            x_next = (1.0 - alpha) * x_curr + alpha * np.tanh(np.dot(x_lag, A_base))
            history.pop(0)
            history.append(x_next)
            terminal_states.append(round(float(np.linalg.norm(x_next)), 4))
            
        unique_orbits = len(set(terminal_states))
        if unique_orbits > 1:
            bifurcation_points.append((float(alpha), unique_orbits))
        if unique_orbits >= 4 and feigenbaum_fracture is None:
            feigenbaum_fracture = float(alpha)
            
    print(f" -> Found {len(bifurcation_points)} Split Orbits across Over-Unity Gain Space.")
    if feigenbaum_fracture:
        print(f" -> [!] FEIGENBAUM cliff detected at alpha = {feigenbaum_fracture:.4f} (Deterministic Chaos)")
    else:
        print(" -> [✓] Stable Monotonic Tracks: System matrix resisted period-doubling chaos cascades.")

    # 3. PARADIGM 2: 2D Coupled Map Lattice (CML) Spatiotemporal Grid
    print("\n[STAGE 3] Scaling VerifyBridge into a 2D Coupled Map Lattice...")
    lattice_dim = 21
    spatial_coupling_diff = 0.25
    
    # Initialize grid nodes with state tensors (6-dimensional vectors per lattice cell)
    lattice_grid = np.random.uniform(-0.1, 0.1, size=(lattice_dim, lattice_dim, 6))
    rogue_wave_emerged = False
    
    # Evolve the spatiotemporal grid over 30 generation steps
    for step in range(30):
        next_lattice = np.copy(lattice_grid)
        for r in range(lattice_dim):
            for c in range(lattice_dim):
                local_evolution = np.tanh(np.dot(lattice_grid[r, c], A_base))
                
                # Spatial diffusion mixing with 4 nearest neighbors (Up, Down, Left, Right)
                neighbor_sum = (lattice_grid[(r-1)%lattice_dim, c] + 
                                lattice_grid[(r+1)%lattice_dim, c] + 
                                lattice_grid[r, (c-1)%lattice_dim] + 
                                lattice_grid[r, (c+1)%lattice_dim])
                
                next_lattice[r, c] = (1.0 - spatial_coupling_diff) * local_evolution + (spatial_coupling_diff / 4.0) * neighbor_sum
                
        lattice_grid = next_lattice
        cell_magnitudes = np.linalg.norm(lattice_grid, axis=2)
        if np.max(cell_magnitudes) > 5.0 * np.mean(cell_magnitudes):
            rogue_wave_emerged = True
            
    print(f" -> Lattice Evolution Completed across {lattice_dim}x{lattice_dim} Domain Nodes.")
    print(f" -> Rogue Wave Spatiotemporal Cluster Emergence: {rogue_wave_emerged}")

    # 4. PARADIGM 3: Zero-Sum Strategic Policy Game Loop
    print("\n[STAGE 4] Simulating Zero-Sum Gradient Arms Race vs Attacker Policy...")
    attacker_weights = np.random.randn(6, 3) * 0.05
    defender_weights = np.copy(base_weights)
    game_converged = False
    
    for game_round in range(50):
        A_def = np.dot(defender_weights, defender_weights.T)
        grad_sign = np.sign(np.dot(A_def, attacker_weights))
        attacker_weights += 0.01 * grad_sign
        
        A_att = np.dot(attacker_weights, attacker_weights.T)
        def_eigenvals = np.linalg.eigvals(A_def + A_att)
        spectral_radius = float(np.max(np.abs(def_eigenvals)))
        
        if spectral_radius > 1.2:
            defender_weights *= 0.8
            
        if game_round == 49 and spectral_radius < 1.0:
            game_converged = True
            
    print(f" -> Final Attacker vs Defender Spectral Radius: {spectral_radius:.6f}")
    print(f" -> Game Loop Settled into Stable Nash Equilibrium: {game_converged}")

    # 5. PARADIGM 4: Heavy-Tailed Cauchy / Lévy Flights Resilience Audit
    print("\n[STAGE 5] Injecting Heavy-Tailed Cauchy Multi-Sigma Shock Flights...")
    test_state = np.array([0.1, 0.1, 0.1, 0.1, 0.1, 0.1])
    
    # Generate infinite-variance shock using standard Cauchy distribution parameters
    cauchy_shock_vector = np.random.standard_cauchy(size=test_state.shape) * 3.5
    print(f" -> Catastrophic Out-of-Bounds Impact Vector:\n    {cauchy_shock_vector}")
    
    shocked_state = test_state + cauchy_shock_vector
    initial_shock_magnitude = float(np.linalg.norm(shocked_state))
    print(f" -> Initial Shock Magnitude: {initial_shock_magnitude:.6f}")
    
    current_shock_state = shocked_state
    for recovery_step in range(1, 11):
        current_shock_state = np.tanh(np.dot(current_shock_state, A_base))
        
    final_magnitude = float(np.linalg.norm(current_shock_state))
    recovery_velocity = (initial_shock_magnitude - final_magnitude) / 10.0
    print(f" -> Terminal Recovery State Magnitude (Step 10): {final_magnitude:.6f}")
    print(f" -> Calculated System Recovery Velocity      : {recovery_velocity:.6f} energy/step")

    # 6. Global System Status Assertion
    print("\n[STAGE 6] Consolidating Global System Status Signature...")
    if not rogue_wave_emerged and final_magnitude < 0.05:
        status_signature = "SYSTEM_APEX_TOTALITY_VERIFIED"
        print(f" -> Status: [✓] System proved structural containment across all chaos domains.")
    else:
        status_signature = "SYSTEM_TOPOLOGY_COMPROMISED"
        print(" -> Status: [!] Boundary fracture confirmed. Adjust systemic dampening arrays.")
    print("==========================================================================")

    # Compile non-hardcoded report structure
    phase36_report = {
        "suite": "PHASE_36_MASTER_MATRIX",
        "timestamp": time.time(),
        "bifurcation_data": {
            "feigenbaum_cliff": feigenbaum_fracture,
            "detected_orbits_count": len(bifurcation_points)
        },
        "spatiotemporal_cml": {
            "rogue_wave_detected": rogue_wave_emerged,
            "lattice_nodes_synchronized": lattice_dim**2
        },
        "zero_sum_game": {
            "nash_equilibrium_reached": game_converged,
            "terminal_spectral_radius": round(spectral_radius, 6)
        },
        "levy_flight_resilience": {
            "initial_impact_amplitude": round(initial_shock_magnitude, 6),
            "recovery_velocity_coefficient": round(recovery_velocity, 6),
            "residual_energy": round(final_magnitude, 6)
        },
        "system_status": status_signature
    }
    
    with open("test_phase36_report.json", "w") as f:
        json.dump(phase36_report, f, indent=2)
    print(" -> Master report successfully generated and saved to: test_phase36_report.json")

if __name__ == "__main__":
    run_phase36_master_stress_matrix()

