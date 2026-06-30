# test_phase29_apex.py
# Phase 29 v3: FIXED — fault magnitude range now calibrated
# below the real veto threshold (~0.00263, confirmed in v2's
# boundary search) so injected faults are actually strong
# enough to test localization/separation, not mostly noise.

import numpy as np
from collections import defaultdict
from PrimeRuntimeV4_backup import PrimeRuntimeV4

print("=" * 60)
print("=== PHASE 29 v3: TWO-FAULT SEPARATION (FIXED RANGE) ===")
print("=" * 60)

def diagnose_multi(veto_log, streak_threshold=3):
    steps = defaultdict(set)
    for step, nid, reason in veto_log:
        steps[step].add((nid, reason))
    if not steps:
        return set()
    streak = defaultdict(int)
    flagged = set()
    lo, hi = min(steps), max(steps)
    for s in range(lo, hi + 1):
        present = steps.get(s, set())
        for key in list(streak.keys()):
            if key not in present:
                streak[key] = 0
        for key in present:
            streak[key] += 1
            if streak[key] >= streak_threshold:
                flagged.add(key[0])
    return flagged

def run_to_vetolog(rt, n_steps):
    veto_log = []
    for t in range(n_steps):
        rt.step(0.05)
        for n in rt.nodes:
            if n.state.n7_gate_status == "Vetoed":
                veto_log.append((t, n.id, n.state.n7_veto_reason))
    return veto_log

print("--- TEST 0: SIMULTANEOUS TWO-NODE FAULT LOCALIZATION ---")
print("    (mass range now 0.0001-0.0020, confirmed below")
print("     the real ~0.00263 veto threshold)")

N_TRIALS_MULTI = 25
both_hit = 0
partial_hit = 0
no_hit = 0
trial_log = []

for trial in range(N_TRIALS_MULTI):
    rng = np.random.default_rng(4000 + trial)
    np.random.seed(4000 + trial)
    rt = PrimeRuntimeV4()

    warmup = int(rng.integers(10, 80))
    for _ in range(warmup):
        rt.step(0.05)

    targets = rng.choice(21, size=2, replace=False)
    mags = [float(rng.uniform(0.0001, 0.0020)) for _ in targets]
    for tid, mag in zip(targets, mags):
        rt.nodes[int(tid)].mass = mag

    run_len = int(rng.integers(200, 400))
    veto_log = run_to_vetolog(rt, run_len)
    flagged = diagnose_multi(veto_log)

    target_set = set(int(t) for t in targets)
    overlap = flagged & target_set
    if len(overlap) == 2:
        both_hit += 1
        outcome = "BOTH"
    elif len(overlap) == 1:
        partial_hit += 1
        outcome = "PARTIAL"
    else:
        no_hit += 1
        outcome = "NONE"
    trial_log.append((trial, sorted(target_set), mags, sorted(flagged), outcome))

for trial, targets, mags, flagged, outcome in trial_log:
    mag_str = [f"{m:.5f}" for m in mags]
    print(f"    trial={trial} targets={targets} mags={mag_str} "
          f"flagged={flagged} {outcome}")

print(f"\n    BOTH_HIT={both_hit}/{N_TRIALS_MULTI} "
      f"PARTIAL={partial_hit}/{N_TRIALS_MULTI} "
      f"NONE={no_hit}/{N_TRIALS_MULTI}")
print("    (raw result, no pass/fail threshold applied)")
print("=" * 60)
