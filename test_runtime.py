# test_runtime.py
import numpy as np

from PrimeRuntimeV4_backup import (
    Node,
    StochasticResonanceNode,
    Dynamics,
    apply_mc2_coupling_cascade,
    sync_weights,
    sync_weights_unweighted,
    sanitize_state,
    clamp_u,
    verify_clamp_u_bound,
    verify_mc2_retain_leak_sum,
    verify_mc2_coupling_symmetric,
    verify_priority_injective,
    system_gate_report,
    policy_at_least_as_permissive,
    find_most_permissive_node,
    quantum_density_matrix,
    quantum_is_hermitian,
    quantum_trace_one,
    quantum_is_positive,
    quantum_unitary_evolve,
    quantum_trace_preserved,
    lawson_satisfied,
    alfven_velocity,
    frame_dragging,
    n7_gate_decision,
    manifold21_lyapunov,
    moruzin_chamber_valid,
    IntegrityTracker,
    EnergyTriad,
)


def test_energy_triad():
    triad = EnergyTriad(energy=1.0, thermal=-5.0, structural=2.0)
    assert triad.thermal == 0.0, "EnergyTriad should clamp negative thermal to 0"
    assert triad.total == 3.0
    print("test_energy_triad: OK")


def test_mc2_identities():
    r1 = verify_mc2_retain_leak_sum()
    assert r1["matches_proven_identity"], r1
    r2 = verify_mc2_coupling_symmetric()
    assert r2["symmetric"], r2
    print("test_mc2_identities: OK", r1, r2)


def test_clamp_u_bound():
    result = verify_clamp_u_bound(num_trials=500)
    assert result["bound_holds"], result
    print("test_clamp_u_bound: OK", result)


def test_sanitize_state():
    bad = np.array([np.nan, np.inf, -np.inf, 3.0])
    cleaned = sanitize_state(bad, fallback=0.0)
    assert not np.any(np.isnan(cleaned))
    assert not np.any(np.isinf(cleaned))
    assert cleaned[3] == 3.0
    print("test_sanitize_state: OK", cleaned)


def test_priority_injective():
    nodes = [Node(i) for i in range(21)]
    ok, dupes = verify_priority_injective(nodes)
    assert ok, f"priority collision found: {dupes}"
    print("test_priority_injective: OK, 21 unique priorities")


def test_system_gate_report():
    report_clean = system_gate_report(["Sealed", "Sealed", "Sealed"])
    assert report_clean["system_status"] == "Sealed"
    assert report_clean["forward_reverse_consistent"]

    report_vetoed = system_gate_report(["Sealed", "Vetoed", "Sealed"])
    assert report_vetoed["system_status"] == "Vetoed"
    assert report_vetoed["veto_causing_nodes"] == [1]
    assert report_vetoed["forward_reverse_consistent"]
    print("test_system_gate_report: OK", report_clean, report_vetoed)


def test_permissive_ordering():
    nodes = [StochasticResonanceNode(i, noise_level=0.01 * (i + 1)) for i in range(4)]
    for i, n in enumerate(nodes):
        n.state.local_margin = float(i)
    most = find_most_permissive_node(nodes)
    assert most == 3, f"expected node 3 (highest noise+margin), got {most}"
    print("test_permissive_ordering: OK, most permissive node index =", most)


def test_quantum_channel():
    x_state = np.array([1.0, 1.0])
    rho = quantum_density_matrix(x_state)
    assert quantum_is_hermitian(rho)
    assert quantum_trace_one(rho)
    assert quantum_is_positive(rho)

    rho_evolved = quantum_unitary_evolve(rho, theta=0.7)
    assert quantum_is_hermitian(rho_evolved)
    assert quantum_trace_preserved(rho, rho_evolved)
    print("test_quantum_channel: OK")


def test_physics_helpers():
    assert lawson_satisfied(1e20, 1e2, 1e0) is False
    assert lawson_satisfied(1e21, 1e1, 1e1) is True
    v_a = alfven_velocity(B_field=1.0, mu_zero=1.0, rho=1.0)
    assert v_a == 1.0
    fd = frame_dragging(0.0)
    assert fd == 1.0
    status, veto_idx = n7_gate_decision([0.5, 0.9, 0.3], floor=0.2)
    assert status == "Sealed"
    status2, veto_idx2 = n7_gate_decision([0.5, 0.1, 0.3], floor=0.2)
    assert status2 == "Vetoed" and veto_idx2 == 1
    print("test_physics_helpers: OK")


def test_manifold_and_chamber():
    q = np.array([1.0, 2.0])
    p = np.array([0.5, 0.5])
    q_eq = np.zeros(2)
    p_eq = np.zeros(2)
    V = manifold21_lyapunov(q, p, q_eq, p_eq)
    assert V > 0.0
    assert moruzin_chamber_valid(delta=0.5, m_eff=1.0) is True
    assert moruzin_chamber_valid(delta=5.0, m_eff=1.0) is False
    print("test_manifold_and_chamber: OK, lyapunov =", V)


def test_integrity_tracker():
    tracker = IntegrityTracker()
    assert tracker.check_transition(True, True) is True
    assert tracker.check_transition(False, False) is True
    assert tracker.check_transition(True, False) is False
    assert tracker.integrity_ever_broken is True
    print("test_integrity_tracker: OK")


def test_dynamics_step_single_node():
    node = Node(0)
    node.state.x = np.array([1.0, 0.0, 0.0])
    dyn = Dynamics()
    for _ in range(5):
        dyn.step(node, dt=0.01)
    assert not np.any(np.isnan(node.state.x))
    assert not np.any(np.isnan(node.state.p))
    assert isinstance(node.state.hamiltonian, float)
    print("test_dynamics_step_single_node: OK, hamiltonian =", node.state.hamiltonian)


def test_dynamics_with_links_and_coupling_cascade():
    n0 = Node(0)
    n1 = StochasticResonanceNode(1, noise_level=0.05)
    n2 = Node(2)
    n0.links = [n1, n2]
    n1.links = [n0]
    n2.links = [n0]

    n0.state.x = np.array([2.0, 0.0, 0.0])
    n1.state.x = np.array([0.0, 1.0, 0.0])
    n2.state.x = np.array([0.0, 0.0, 1.0])

    dyn = Dynamics()
    for _ in range(10):
        for n in (n0, n1, n2):
            dyn.step(n, dt=0.02)

    for n in (n0, n1, n2):
        assert not np.any(np.isnan(n.state.x)), f"node {n.id} x has NaN"
        assert not np.any(np.isnan(n.state.u)), f"node {n.id} u has NaN"
        norm_u = float(np.linalg.norm(n.state.u))
        assert norm_u <= 0.99 + 1e-9, f"node {n.id} u norm {norm_u} exceeds clamp"

    apply_mc2_coupling_cascade([n0, n1, n2])
    for n in (n0, n1, n2):
        assert n.state.mc2_leaked_delta.shape == (3,)
        assert not np.any(np.isnan(n.state.mc2_leaked_delta))

    print("test_dynamics_with_links_and_coupling_cascade: OK")
    print("  n0.u =", n0.state.u, "n0.leaked =", n0.state.mc2_leaked_delta)
    print("  n1.u =", n1.state.u, "n1.leaked =", n1.state.mc2_leaked_delta)
    print("  n2.u =", n2.state.u, "n2.leaked =", n2.state.mc2_leaked_delta)


def test_sync_weights_convergence():
    nodes = [Node(i) for i in range(5)]
    for i, n in enumerate(nodes):
        n.state.local_margin = float(i)
        n.policy.weights = np.full((6, 3), float(i))

    before = np.array([n.policy.weights.copy() for n in nodes])
    sync_weights(nodes, eta=0.5)
    after = np.array([n.policy.weights.copy() for n in nodes])
    assert not np.allclose(before, after), "sync_weights should change weights"

    nodes2 = [Node(i) for i in range(5)]
    for i, n in enumerate(nodes2):
        n.policy.weights = np.full((6, 3), float(i))
    sync_weights_unweighted(nodes2, eta=1.0)
    avg_expected = np.mean([float(i) for i in range(5)])
    for n in nodes2:
        assert np.allclose(n.policy.weights, avg_expected, atol=1e-6)

    print("test_sync_weights_convergence: OK")


def test_apply_ssr_noise_is_live():
    node = StochasticResonanceNode(0, noise_level=0.5)
    np.random.seed(42)
    state_vec = np.zeros(6)

    node.policy.weights = np.ones((6, 3))
    plain_output = node.policy.act(state_vec)

    noisy_outputs = [node.apply_ssr(state_vec) for _ in range(20)]
    all_equal_to_plain = all(
        np.allclose(out, plain_output) for out in noisy_outputs
    )
    assert not all_equal_to_plain, (
        "apply_ssr outputs matched noiseless policy.act on every trial; "
        "noise term appears inactive"
    )

    spread = np.std(np.array(noisy_outputs), axis=0)
    assert np.any(spread > 1e-6), "apply_ssr outputs show no variance across trials"

    node.noise_level = 0.0
    zero_noise_outputs = [node.apply_ssr(state_vec) for _ in range(5)]
    for out in zero_noise_outputs:
        assert np.allclose(out, plain_output, atol=1e-6), (
            "with noise_level clamped to minimum, apply_ssr should match "
            "policy.act closely"
        )
    print("test_apply_ssr_noise_is_live: OK, output spread =", spread)


def run_all():
    tests = [
        test_energy_triad,
        test_mc2_identities,
        test_clamp_u_bound,
        test_sanitize_state,
        test_priority_injective,
        test_system_gate_report,
        test_permissive_ordering,
        test_quantum_channel,
        test_physics_helpers,
        test_manifold_and_chamber,
        test_integrity_tracker,
        test_dynamics_step_single_node,
        test_dynamics_with_links_and_coupling_cascade,
        test_sync_weights_convergence,
        test_apply_ssr_noise_is_live,
    ]
    passed = 0
    failed = []
    for t in tests:
        try:
            t()
            passed += 1
        except AssertionError as e:
            failed.append((t.__name__, str(e)))
            print(f"{t.__name__}: FAILED -> {e}")

    print("\n----- SUMMARY -----")
    print(f"{passed}/{len(tests)} passed")
    if failed:
        print("Failures:")
        for name, msg in failed:
            print(f"  {name}: {msg}")


if __name__ == "__main__":
    run_all()
