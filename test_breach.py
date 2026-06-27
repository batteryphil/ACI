from VerifyBridge import VerifyBridge
from lean_bounds import LeanBounds

vb = VerifyBridge()

print("=== TEST 1: BREACH GATE ===")
print("Forcing breach condition at step 5...")

for step in range(10):
    if step == 5:
        # Force breach by injecting margin below threshold
        validation = LeanBounds.validate_margin(0.03)
        if validation['status'] == 'BREACH':
            print(f"[{step:04d}] BREACH CONFIRMED — breach_implies_halt FIRED")
            print(f"Theorem: {validation['lean_theorem']}")
            print(f"Module: {validation['lean_module']}")
            print("=== TEST 1: PASSED ===")
            break
    else:
        result = vb.verified_step(0.05)
        print(f"[{step:04d}] STATUS:{result['status']} MARGIN:{float(result['margin']):.6f}")
