from VerifyBridge import VerifyBridge
from lean_bounds import LeanBounds
from aci_runtime_loop import compute_lyapunov
import numpy as np

vb = VerifyBridge()

print("=== PHASE 4: ADVERSARIAL INJECTION ===")
print("Injecting corrupted margins into specific domains...")

results = []

for trial in range(5):
    # Pick a random domain to corrupt
    target_domain = np.random.randint(0, 21)
    
    # Build margins with one domain corrupted below breach threshold
    node_margins = [
        min(1.0 - n.state.sigma * 0.05,
            1.0 - np.linalg.norm(n.state.u),
            1.0 - np.linalg.norm(n.state.x) * 0.1)
        for n in vb.rt.nodes
    ]
    
    # Inject adversarial corruption
    node_margins[target_domain] = 0.02
    
    closure = LeanBounds.domain_closure_check(node_margins)
    M_N7 = float(closure.get('M_N7', 0.0))
    bottleneck = closure.get('bottleneck_domain', -1)
    status = closure.get('status', '')
    theorem = closure.get('lean_theorem', '')
    
    passed = bottleneck == target_domain and M_N7 <= 0.05
    results.append(passed)
    
    print(f"\nTRIAL {trial+1}: Corrupted D{target_domain}")
    print(f"  M_N7: {M_N7:.6f}")
    print(f"  Detected bottleneck: D{bottleneck}")
    print(f"  Status: {status}")
    print(f"  Theorem: {theorem}")
    print(f"  Correctly identified: {'YES' if passed else 'NO'}")

print(f"\n=== PHASE 4 REPORT ===")
print(f"Correct detections: {sum(results)}/5")
print("=== PHASE 4: PASSED ===" if all(results) else "=== PHASE 4: PARTIAL ===")
