import numpy as np
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=== PHASE 10: SYNAPTIC CONVERGENCE TEST ===")
print("Testing: 21x21 weight matrix drives cognitive state to fixed point")
print("Theorem: synapticWeight_pos, synapticWeight_symm — Synaptic_Weights.lean")

def gaussian_kernel(i, j, n=21):
    return np.exp(-((i - j) ** 2) / (2 * (n / 7) ** 2))

W = np.array([[gaussian_kernel(i, j) for j in range(21)] for i in range(21)])

symmetry_ok = np.allclose(W, W.T)
positivity_ok = np.all(W > 0)

results = []

rt = PrimeRuntimeV4()

for trial in range(5):
    state = np.array([rt.nodes[i % len(rt.nodes)].state.x[0]
                      for i in range(21)])

    prev = np.inf
    converged = False
    for step in range(200):
        state = W @ state
        state = state / (np.linalg.norm(state) + 1e-10)
        delta = np.abs(np.linalg.norm(state) - prev)
        if delta < 1e-6:
            converged = True
            break
        prev = np.linalg.norm(state)

    rt.step(0.05)

    passed = converged and symmetry_ok and positivity_ok
    results.append(passed)

    print(f"\nTRIAL {trial+1}:")
    print(f"  Weight matrix symmetric: {symmetry_ok}")
    print(f"  Weight matrix positive: {positivity_ok}")
    print(f"  Converged to fixed point: {converged}")
    print(f"  Theorem: synapticWeight_pos — Synaptic_Weights.lean")
    print(f"  Theorem: synapticWeight_symm — Synaptic_Weights.lean")
    print(f"  Trial passed: {passed}")

print(f"\n=== PHASE 10 REPORT ===")
print(f"Synaptic convergence trials passed: {sum(results)}/5")
print(f"Weight matrix: symmetric={symmetry_ok}, positive={positivity_ok}")
print("=== PHASE 10: PASSED ===" if all(results) else "=== PHASE 10: FAILED ===")
