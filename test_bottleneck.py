from VerifyBridge import VerifyBridge
from lean_bounds import LeanBounds
from aci_runtime_loop import compute_lyapunov
import numpy as np

vb = VerifyBridge()

print("=== TEST 3: DOMAIN STRESS — BOTTLENECK DETECTION ===")

domain_hits = {}
for i in range(21):
    domain_hits[i] = 0

for step in range(200):
    result = vb.verified_step(0.05)
    margin = float(result['margin'])

    node_margins = [
        min(1.0 - n.state.sigma * 0.05,
            1.0 - np.linalg.norm(n.state.u),
            1.0 - np.linalg.norm(n.state.x) * 0.1)
        for n in vb.rt.nodes
    ]

    closure = LeanBounds.domain_closure_check(node_margins)
    bottleneck = closure.get('bottleneck_domain', -1)
    M_N7 = float(closure.get('M_N7', 0.0))

    if bottleneck >= 0:
        domain_hits[bottleneck] += 1

    if step % 50 == 0:
        print(f"[{step:04d}] STATUS:{result['status']} M_N7:{M_N7:.6f} BOTTLENECK:D{bottleneck}")

print("\n=== BOTTLENECK FREQUENCY REPORT ===")
sorted_domains = sorted(domain_hits.items(), key=lambda x: x[1], reverse=True)
for domain, hits in sorted_domains[:5]:
    print(f"D{domain}: {hits} times ({hits/200*100:.1f}%)")

print("\n=== TEST 3: PASSED ===" if max(domain_hits.values()) > 0 else "=== TEST 3: FAILED ===")
