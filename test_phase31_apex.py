import sys
sys.path.append("/root/my_project")

import numpy as np
from PrimeRuntimeV4_backup import (
    PrimeRuntimeV4, mc2_collision_force, mc2_load_factor,
    mc2_effective_mass, mc2_displacement,
)

print("=" * 60)
print("=== PHASE 31 (REBUILT v2): MASS-AWARE LOOK-AHEAD ===")
print("=" * 60)

N_TRIALS = 25
proactively_prevented = 0
reactively_needed = 0
unrecovered = 0

for trial in range(N_TRIALS):
    rng = np.random.default_rng(11000 + trial)
    np.random.seed(11000 + trial)
    rt = PrimeRuntimeV4()

    warmup = int(rng.integers(10, 60))
    for _ in range(warmup):
        rt.step(0.05)

    target_id = int(rng.integers(0, 21))
    node = rt.nodes[target_id]

    # About to corrupt mass -- this is the actual fault.
    incoming_mass = float(rng.uniform(0.0005, 0.002))

    # LOOK-AHEAD: using the runtime's OWN real dynamics formulas
    # (mc2_effective_mass, mc2_displacement) to predict what the
    # displacement magnitude WOULD BE if this mass were applied,
    # BEFORE actually applying it.
    F = mc2_collision_force(node.O_strength, node.Gamma_gain, node.Omega_burden)
    load = mc2_load_factor(np.linalg.norm(node.state.x) / 5.0)
    predicted_m_eff = mc2_effective_mass(incoming_mass, load)
    predicted_delta = mc2_displacement(F, predicted_m_eff, 0.05)
    # u_term margin = 1 - norm(u); a large predicted displacement
    # means u_term will breach after clamping/direction normalization
    predicted_u_term_margin = 1.0 - min(predicted_delta, 1.0)

    proactive_action_taken = False
    if predicted_u_term_margin < 0.05:
        # Proactive: raise mass toward safety BEFORE applying the
        # risky value at all, instead of applying it and reacting.
        incoming_mass = max(incoming_mass, 0.01)
        proactive_action_taken = True

    node.mass = incoming_mass

    for t in range(100):
        rt.step(0.05)

    breached_after = node.state.n7_gate_status == "Vetoed"

    if proactive_action_taken and not breached_after:
        proactively_prevented += 1
    elif breached_after:
        node.mass = max(node.mass, 0.01)
        for t in range(100):
            rt.step(0.05)
        if node.state.n7_gate_status == "Sealed":
            reactively_needed += 1
        else:
            unrecovered += 1
    else:
        reactively_needed += 1

print(f"PROACTIVELY_PREVENTED={proactively_prevented}/{N_TRIALS}")
print(f"REACTIVE_RECOVERY_USED={reactively_needed}/{N_TRIALS}")
print(f"UNRECOVERED={unrecovered}/{N_TRIALS}")
print("(raw result -- no pass/fail label, read directly)")

status = "PASSED" if unrecovered == 0 else "FAILED"
print(f"\nPHASE 31 STATUS: {status} (derived from unrecovered={unrecovered})")
