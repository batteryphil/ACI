import sys
sys.path.append("/root/my_project")

import numpy as np
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 30 (REBUILT): FAULT INJECTION + REMEDIATION ===")
print("=" * 60)
print("(FSI.lean verification happens via CI on push, not here --")
print(" local Lean compilation is never run on this device.)")
print()

N_TRIALS = 25
recovered = 0
not_recovered = 0

for trial in range(N_TRIALS):
    rng = np.random.default_rng(9000 + trial)
    np.random.seed(9000 + trial)
    rt = PrimeRuntimeV4()

    warmup = int(rng.integers(10, 60))
    for _ in range(warmup):
        rt.step(0.05)

    target_id = int(rng.integers(0, 21))
    rt.nodes[target_id].mass = float(rng.uniform(0.0005, 0.002))

    for t in range(100):
        rt.step(0.05)

    faulted = rt.nodes[target_id].state.n7_gate_status == "Vetoed"

    if faulted:
        rt.nodes[target_id].mass = max(rt.nodes[target_id].mass, 0.01)

    for t in range(100):
        rt.step(0.05)

    cleared = rt.nodes[target_id].state.n7_gate_status == "Sealed"
    if cleared:
        recovered += 1
    else:
        not_recovered += 1

print(f"RECOVERED={recovered}/{N_TRIALS} NOT_RECOVERED={not_recovered}/{N_TRIALS}")
print("(raw result -- no pass/fail label, read directly)")
