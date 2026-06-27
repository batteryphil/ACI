from VerifyBridge import VerifyBridge
from aci_runtime_loop import compute_lyapunov
import numpy as np

vb = VerifyBridge()

print("=== TEST 2: LONG-TERM STABILITY — 1000 STEPS ===")

lyapunov_values = []
breach_count = 0
degraded_count = 0
stable_count = 0

for step in range(1000):
    result = vb.verified_step(0.05)
    status = result['status']
    lyap = compute_lyapunov(vb.rt.nodes)
    lyapunov_values.append(lyap)

    if status == 'HALT':
        breach_count += 1
        print(f"[{step:04d}] BREACH — system halted")
        break
    elif status == 'DEGRADED':
        degraded_count += 1
    else:
        stable_count += 1

    if step % 100 == 0:
        print(f"[{step:04d}] STABLE:{stable_count} DEGRADED:{degraded_count} LYAPUNOV:{lyap:.6f} MAX:{max(lyapunov_values):.6f}")

print(f"\nFINAL REPORT:")
print(f"STABLE steps: {stable_count}")
print(f"DEGRADED steps: {degraded_count}")
print(f"BREACH events: {breach_count}")
print(f"Lyapunov MAX: {max(lyapunov_values):.6f}")
print(f"Lyapunov FINAL: {lyapunov_values[-1]:.6f}")
print("=== TEST 2: PASSED ===" if breach_count == 0 else "=== TEST 2: BREACH DETECTED ===")
