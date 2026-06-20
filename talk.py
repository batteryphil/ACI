from VerifyBridge import VerifyBridge
bridge = VerifyBridge()
print('Sovereign Kernel Active. Awaiting input.')
while True:
    user_input = input('> ')
    if user_input.lower() == 'exit': break
    print(bridge.talk(user_input))
