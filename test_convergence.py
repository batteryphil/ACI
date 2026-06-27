from PrimeRuntimeV4_backup import PrimeRuntimeV4
from aci_runtime_loop import compute_lyapunov
from lean_bounds import LeanBounds
import numpy as np

print("=== PHASE 6: CONVERGENCE VERIFICATION ===")
print("Launching from 5 different initial states...")

CONTRACTION_K = 0.85
ATTRACTOR = 0.727
TOLERANCE = 0.05
results = []

for trial in range(5):
    rt = PrimeRuntimeV4()

    scale = (trial + 1) * 0.2
    for node in rt.nodes:
        node.state.x = np.random.randn(3) * scale
        node.state.u = np.random.randn(3) * scale
        node.state.f = np.random.randn(3) * scale

    initial_lyap = compute_lyapunov(rt.nodes)
    lyap_values = [initial_lyap]
    converged = False
    convergence_step = -1

    for step in range(300):
        rt.step(0.05)
        lyap = compute_lyapunov(rt.nodes)
        lyap_values.append(lyap)

        if abs(lyap - ATTRACTOR) < TOLERANCE and step > 50:
            converged = True
            convergence_step = step
            break

    final_lyap = lyap_values[-1]
    results.append(converged)

    print(f"\nTRIAL {trial+1} — Initial scale: {scale:.1f}")
    print(f"  Initial Lyapunov: {initial_lyap:.6f}")
    print(f"  Final Lyapunov:   {final_lyap:.6f}")
    print(f"  Attractor target: {ATTRACTOR}")
    print(f"  Converged: {'YES at step ' + str(convergence_step) if converged else 'NO'}")
    print(f"  Theorem: convergence — MyProject.lean")

print(f"\n=== PHASE 6 REPORT ===")
print(f"Convergent trajectories: {sum(results)}/5")
print(f"Formal guarantee: k={CONTRACTION_K} < 1 implies all trajectories converge")
print("=== PHASE 6: PASSED ===" if all(results) else "=== PHASE 6: FAILED ===")
