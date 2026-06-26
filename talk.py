from VerifyBridge import VerifyBridge

bridge = VerifyBridge()
print('Sovereign Kernel Active. Awaiting input.')

while True:
    user_input = input('> ')
    if user_input.lower() == 'exit':
        break
    result = bridge.verified_step(0.05)
    report = bridge.full_report()
    print(f"STATUS: {result['status']}")
    print(f"MARGIN: {float(result['margin']):.6f}")
    print(f"MANIFOLD: {report['manifold']}")
    print(f"RUNTIME: {report['runtime']}")
