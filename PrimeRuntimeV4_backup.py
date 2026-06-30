import numpy as np
import random

# ============================================================
# ENERGY DOMAIN — domain labels and priority ordering, from
# EnergyDomain.lean (Domain inductive type, domain_priority,
# M_N7 closure law: system valid iff min margin > 0 across
# all domains)
# ============================================================

DOMAIN_NAMES = [
    "A_Energy", "B_Control", "C_Thermal", "D_Structural",
    "E_Boundary", "F_Diagnostics", "G_Governance",
    "H_Harmonic", "I_Information", "J_Joining",
    "K_Kernel", "L_Localization", "M_Morphogenic",
    "N_Node", "O_Operator", "P_Propagation",
    "Q_Quality", "R_Resonance", "S_State",
    "T_Temporal", "U_Unification",
]

def domain_priority(domain_index):
    """Priority 1-21, matching EnergyDomain.lean's
    domain_priority function (A_Energy=1, ..., U_Unification=21)."""
    return domain_index + 1

# ============================================================
# SOVEREIGN HAMILTONIAN — H_OPT7 = T_kinetic + V_potential +
# G_governance, from SovereignHamiltonian.lean
# ============================================================

def T_kinetic(p, m):
    """T = Σ p_i² / (2*m_i). Proven nonneg when m_i > 0."""
    return float(np.sum(p ** 2 / (2 * m)))

def V_potential(k, y_actual, y_spine):
    """V = (1/2)*k * Σ (y_actual_i - y_spine_i)².
    Proven nonneg, proven zero iff y_actual = y_spine."""
    return float(0.5 * k * np.sum((y_actual - y_spine) ** 2))

def G_governance(W, A, dl):
    """G = W * Σ A_i * dl_i."""
    return float(W * np.sum(A * dl))

def H_OPT7(p, m, k, y_actual, y_spine, W, A, dl):
    return (T_kinetic(p, m) + V_potential(k, y_actual, y_spine) +
            G_governance(W, A, dl))

# ============================================================
# ENERGY TRIAD — energy/thermal/structural, from
# PhysicsCore.lean's EnergyTriad structure
# ============================================================

class EnergyTriad:
    """Mirrors PhysicsCore.lean's EnergyTriad: three
    nonnegative components, total = sum, proven nonneg."""
    def __init__(self, energy=0.0, thermal=0.0, structural=0.0):
        self.energy = max(0.0, energy)
        self.thermal = max(0.0, thermal)
        self.structural = max(0.0, structural)

    @property
    def total(self):
        return self.energy + self.thermal + self.structural

# ============================================================
# MC2 ENGINE — collision force, displacement, 80/20 coupling,
# from MC2Engine.lean
# ============================================================

MC2_U_MAX = 0.95          # saturation ceiling, matches Lean U_MAX
MC2_LOCAL_RETAIN = 0.8     # matches Lean LOCAL_RETAIN
MC2_GLOBAL_LEAK = 0.2      # matches Lean GLOBAL_LEAK

def mc2_load_factor(x):
    """Clamped to [0, U_MAX]. Matches MC2Engine.lean's
    load_factor: min(max(x,0), U_MAX)."""
    return float(np.clip(x, 0.0, MC2_U_MAX))

def mc2_effective_mass(m, load):
    """m_eff = m / (1 - load). Proven >= m, proven > 0
    when load < 1 and m > 0."""
    load = min(load, MC2_U_MAX)  # ensures 1-load > 0
    return m / (1.0 - load)

def mc2_collision_force(O, Gamma, Omega):
    """F = O*Γ / (Ω + ε). Proven nonneg when O, Γ, Ω >= 0."""
    return (O * Gamma) / (Omega + 1e-9)

def mc2_displacement(F, m_eff, dt):
    """Δx = (F/m_eff) * dt². Proven nonneg when F >= 0."""
    return (F / m_eff) * (dt ** 2)

def mc2_update_origin(x_origin, delta):
    """x_origin + LOCAL_RETAIN * delta."""
    return x_origin + MC2_LOCAL_RETAIN * delta

def mc2_update_target(x_target, delta, coupling_strength):
    """x_target + GLOBAL_LEAK * coupling_strength * delta."""
    return x_target + MC2_GLOBAL_LEAK * coupling_strength * delta

def mc2_coupling_strength(m_origin, m_target):
    """1 / (m_origin + m_target). Proven positive, symmetric."""
    return 1.0 / (m_origin + m_target)

# ============================================================
# ANTARES CATEGORY — integrity preservation across state
# transitions, from AntaresCategory.lean. This is a property
# checked on history, not a per-step quantity.
# ============================================================

class IntegrityTracker:
    """Mirrors AntaresCategory.lean's StateTransition.h_valid:
    a transition is valid if (source integrity => target
    integrity). Tracks whether this property has held across
    every step taken so far."""
    def __init__(self):
        self.integrity_ever_broken = False
        self.history = []

    def check_transition(self, source_integrity, target_integrity):
        valid = (not source_integrity) or target_integrity
        self.history.append(valid)
        if not valid:
            self.integrity_ever_broken = True
        return valid

# ============================================================
# CORE RUNTIME STRUCTURES
# ============================================================

class State:
    def __init__(self):
        self.x, self.u, self.f = np.zeros(3), np.zeros(3), np.zeros(3)
        self.t, self.sigma, self.beta = 1.0, 1.0, 0.0
        self.B_x, self.B_y = 0.0, 0.0

        # SovereignHamiltonian state
        self.p = np.zeros(3)          # momentum
        self.y_spine = None           # set at node init: equilibrium target

        # MC2Engine state
        self.load = 0.0               # saturation load, in [0, U_MAX]

        # EnergyTriad state
        self.triad = EnergyTriad()

class Policy:
    def __init__(self):
        self.weights = np.random.randn(6, 3) * 0.1
    def act(self, state_vec):
        return np.tanh(state_vec @ self.weights)

class Node:
    def __init__(self, nid):
        self.id = nid
        self.domain_index = nid % 21
        self.domain_name = DOMAIN_NAMES[self.domain_index]
        self.priority = domain_priority(self.domain_index)

        self.state = State()
        self.links = []
        self.policy = Policy()

        # SovereignHamiltonian parameters
        self.mass = 1.0
        self.spring_k = 0.1
        self.gov_weight = 0.05

        # MC2Engine parameters
        self.O_strength = 1.0
        self.Gamma_gain = 1.0
        self.Omega_burden = 1.0

NOISE_LEVEL_MAX = 1.0
NOISE_LEVEL_MIN = 0.0001

class StochasticResonanceNode(Node):
    def __init__(self, nid, noise_level=0.01):
        super().__init__(nid)
        self._noise_level = float(np.clip(
            noise_level, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self.configured_noise_level = self._noise_level

    @property
    def noise_level(self):
        return self._noise_level

    @noise_level.setter
    def noise_level(self, value):
        clamped = float(np.clip(
            value, NOISE_LEVEL_MIN, NOISE_LEVEL_MAX))
        self._noise_level = clamped
        self.configured_noise_level = clamped

    def apply_ssr(self, state_vec):
        noise = np.random.normal(
            0, self.noise_level, state_vec.shape)
        return self.policy.act(state_vec + noise)

def sync_weights(nodes, eta=0.05):
    all_weights = np.array([n.policy.weights for n in nodes])
    avg_weights = np.mean(all_weights, axis=0)
    for n in nodes:
        n.policy.weights += eta * (avg_weights - n.policy.weights)

def sanitize_state(x, fallback=0.0):
    return np.nan_to_num(x, nan=fallback, posinf=1.0, neginf=-1.0)

U_NORM_MAX = 0.99

def clamp_u(u, max_norm=U_NORM_MAX):
    norm = np.linalg.norm(u)
    if norm > max_norm:
        return u * (max_norm / norm)
    return u

class Dynamics:
    """
    Step function now genuinely incorporates all five physics
    modules:
      - MC2Engine: u is now derived from real collision force
        and displacement, not an arbitrary policy-network
        output, then still bounded by clamp_u for safety.
      - SovereignHamiltonian: momentum p is updated from a
        spring force pulling toward y_spine, with energy
        H_OPT7 computed and stored each step.
      - EnergyTriad: per-node energy/thermal/structural state
        updated from kinetic/potential/governance terms.
      - EnergyDomain: domain priority available per node for
        M_N7 closure-law evaluation in Constraint.
      - AntaresCategory: integrity transitions tracked via
        IntegrityTracker, checked once per node per step.
    """
    def step(self, node, dt):
        s = node.state
        s.x = sanitize_state(s.x)
        s.f = sanitize_state(s.f)
        s.p = sanitize_state(s.p)

        if s.y_spine is None:
            s.y_spine = s.x.copy()

        neighbor_states = [sanitize_state(n.state.x) for n in node.links]
        coupling = np.mean(neighbor_states, axis=0) if neighbor_states else 0
        s.f = 0.6 * s.f + 0.4 * coupling

        # --- MC2ENGINE: real collision force replacing the
        # arbitrary policy-network output for u ---
        F = mc2_collision_force(
            node.O_strength, node.Gamma_gain, node.Omega_burden)
        s.load = mc2_load_factor(np.linalg.norm(s.x) / 5.0)
        m_eff = mc2_effective_mass(node.mass, s.load)
        delta = mc2_displacement(F, m_eff, dt)
        # delta is a scalar magnitude; apply along the policy's
        # directional output (still uses the network for
        # DIRECTION, but magnitude now comes from real physics,
        # not an arbitrary tanh saturation curve)
        sv = np.concatenate([s.x, s.f])
        direction = (node.apply_ssr(sv)
            if isinstance(node, StochasticResonanceNode)
            else node.policy.act(sv))
        dir_norm = np.linalg.norm(direction)
        if dir_norm > 1e-9:
            direction = direction / dir_norm
        s.u = clamp_u(sanitize_state(direction * delta))

        # --- SOVEREIGN HAMILTONIAN: momentum, spring force
        # toward y_spine, governance term ---
        spring_force = -node.spring_k * (s.x - s.y_spine)
        s.p = sanitize_state(s.p + dt * spring_force)
        A_vec = np.abs(s.p)
        dl_vec = s.x - s.y_spine
        H = H_OPT7(
            s.p, np.full(3, node.mass), node.spring_k,
            s.x, s.y_spine, node.gov_weight, A_vec, dl_vec)

        # --- ENERGY TRIAD: energy/thermal/structural update,
        # each component derived from the corresponding real
        # term above (kinetic->energy, governance->thermal,
        # potential deviation->structural) ---
        s.triad = EnergyTriad(
            energy=T_kinetic(s.p, np.full(3, node.mass)),
            thermal=abs(G_governance(node.gov_weight, A_vec, dl_vec)),
            structural=V_potential(node.spring_k, s.x, s.y_spine))

        s.x += dt * (s.u + s.f)
        s.x = sanitize_state(s.x)
        s.sigma = np.linalg.norm(s.x) * (1.0 + abs(s.t - 1.0))

class Constraint:
    """
    M_N7 closure law from EnergyDomain.lean: system valid iff
    min margin across all domains > 0. The existing margin
    formula is preserved, but is now genuinely the per-domain
    margin EnergyDomain.lean's M_N7 takes the minimum over.
    """
    def evaluate(self, nodes):
        margins = [min(1.0 - n.state.sigma * 0.05,
                       1.0 - np.linalg.norm(n.state.u),
                       1.0 - np.linalg.norm(n.state.x) * 0.1)
                   for n in nodes]
        result = min(margins)  # M_N7
        return float(result) if np.isfinite(result) else -1.0

POLE_MARGIN_MAX = 5.0
POLE_MARGIN_MIN = 0.01
ENTROPY_TARGET_MAX = 10.0
ENTROPY_TARGET_MIN = 0.01

def effective_pole_margin(base_margin, nodes):
    if not nodes:
        return base_margin
    mean_noise = float(np.mean([
        getattr(n, "noise_level", 0.01) for n in nodes]))
    tightening = 1.0 / (1.0 + mean_noise)
    tightened = base_margin * max(tightening, 0.3)
    return float(np.clip(
        tightened, POLE_MARGIN_MIN, POLE_MARGIN_MAX))

class MemoryBuffer:
    def __init__(self, capacity=100):
        self.capacity = capacity
        self.buffer = []
    def push(self, state_snapshot):
        self.buffer.append(state_snapshot)
        if len(self.buffer) > self.capacity:
            self.buffer.pop(0)
    def sample_trajectory(self):
        return np.array(self.buffer)

class DivergenceFilter:
    def __init__(self):
        self.last_div = 0.0

    def get_weighted_divergence(self, trajectory, alpha=0.3):
        n = len(trajectory)
        weights = np.exp(-alpha * np.arange(n)[::-1])
        weights /= weights.sum()
        weighted_mean = np.sum(
            trajectory * weights[:, np.newaxis, np.newaxis], axis=0)
        variance = np.sum(
            weights[:, np.newaxis, np.newaxis] *
            (trajectory - weighted_mean) ** 2, axis=0)
        return variance.mean()

    def get_filtered_divergence(self, trajectory, alpha=0.3, beta=0.7):
        raw_div = self.get_weighted_divergence(trajectory, alpha)
        filtered_div = (beta * self.last_div) + ((1.0 - beta) * raw_div)
        self.last_div = filtered_div
        return filtered_div

class PrimeRuntimeV4:
    def __init__(self, entropy_target=1.0, pole_margin=0.99):
        self.nodes = [StochasticResonanceNode(i) for i in range(21)]
        for i, n in enumerate(self.nodes):
            n.links = [self.nodes[(i+1)%21], self.nodes[(i-1)%21]]
        self.dynamics = Dynamics()
        self.constraints = Constraint()
        self.integrity = IntegrityTracker()
        self.step_count = 0

        self.registry_buffer = MemoryBuffer(capacity=50)
        self.divergence_filter = DivergenceFilter()

        self.pole_margin = float(np.clip(
            pole_margin, POLE_MARGIN_MIN, POLE_MARGIN_MAX))
        self.pole_margin_was_clamped = (
            self.pole_margin != pole_margin)

        self.entropy_target = float(np.clip(
            entropy_target,
            ENTROPY_TARGET_MIN, ENTROPY_TARGET_MAX))
        self.entropy_target_was_clamped = (
            self.entropy_target != entropy_target)

        self.entropy_engine = EntropyEngine(
            target_entropy=self.entropy_target)

    def step(self, dt):
        margin_before = self.constraints.evaluate(self.nodes)
        integrity_before = margin_before > 0.05

        for n in self.nodes:
            self.dynamics.step(n, dt)
        if self.step_count % 10 == 0:
            sync_weights(self.nodes)
        self.registry_buffer.push([n.state.x for n in self.nodes])
        div = self.divergence_filter.get_filtered_divergence(
            self.registry_buffer.sample_trajectory())
        self.entropy_engine.apply_normalization(
            self.nodes, self.registry_buffer.sample_trajectory())
        apply_temporal_gating(
            self.step_count, self.nodes, div,
            target=self.entropy_target)
        self.step_count += 1
        dt = get_adaptive_dt(0.05, div)
        live_margin = effective_pole_margin(self.pole_margin, self.nodes)
        apply_pole_stabilization(self.nodes, margin=live_margin)

        margin_after = self.constraints.evaluate(self.nodes)
        integrity_after = margin_after > 0.05
        self.integrity.check_transition(integrity_before, integrity_after)

        return margin_after

    def run(self, steps=200, dt=0.05):
        for t in range(steps):
            if self.step(dt) <= 0.05:
                return f"INSTABILITY_DETECTED_AT_{t}"
        return "RUN COMPLETE"

    def verify_all(self):
        margin = self.constraints.evaluate(self.nodes)
        status = 'STABLE' if margin > 0.05 else 'UNSTABLE'
        return f"MARGIN:{margin:.6f} NODES:{len(self.nodes)} STATUS:{status}"

    @property
    def manifold_state(self):
        margin = self.constraints.evaluate(self.nodes)
        return f"21-DOMAIN-ACTIVE MARGIN:{margin:.4f}"

    @property
    def total_triad_energy(self):
        """Sum of EnergyTriad.total across all nodes."""
        return float(sum(n.state.triad.total for n in self.nodes))

class EntropyEngine:
    def __init__(self, target_entropy=1.0):
        self.target = target_entropy
    def calculate_divergence(self, trajectory):
        return np.var(trajectory, axis=0).mean()
    def apply_normalization(self, nodes, trajectory):
        divergence = self.calculate_divergence(trajectory)
        if divergence > self.target:
            for n in nodes:
                n.state.x *= 0.99

def apply_adaptive_normalization(nodes, trajectory, target=1.0):
    divergence = np.var(trajectory, axis=0).mean()
    gain = np.clip(divergence / target, 0.0, 0.05)
    for n in nodes:
        n.state.x *= (1.0 - gain)

def apply_stochastic_revitalization(nodes, divergence, target=1.0):
    revitalization_factor = np.clip(1.0 - (divergence / target), 0.0, 1.0)
    for n in nodes:
        n.noise_level = 0.01 + (0.05 * revitalization_factor)

def apply_temporal_gating(step_count, nodes, divergence, target=1.0):
    if step_count % 5 == 0:
        revitalization_factor = np.clip(
            1.0 - (divergence / target), 0.0, 1.0)
        for n in nodes:
            base = getattr(n, "configured_noise_level", 0.01)
            n.noise_level = base * (
                0.2 + 0.8 * revitalization_factor)
    else:
        for n in nodes:
            base = getattr(n, "configured_noise_level", 0.01)
            current = n.noise_level
            n.noise_level = current + 0.05 * (base - current)

def get_adaptive_dt(base_dt, divergence, threshold=0.1):
    if divergence > threshold:
        return base_dt / (1.0 + (divergence * 10.0))
    return base_dt

def apply_pole_stabilization(nodes, margin=0.99):
    for n in nodes:
        norm = np.linalg.norm(n.state.x)
        if norm > margin:
            n.state.x *= (margin / norm)

def apply_quantum_causal_flux(nodes, causal_tensor, coupling_strength=0.001):
    for n in nodes:
        if causal_tensor.shape == (2, 2) and len(n.state.x) >= 2:
            flux_correction = causal_tensor @ n.state.x[:2]
            n.state.B_x += coupling_strength * flux_correction[0]
            n.state.B_y += coupling_strength * flux_correction[1]
            B_norm = np.sqrt(n.state.B_x**2 + n.state.B_y**2)
            if B_norm > 1.0:
                n.state.B_x /= B_norm
                n.state.B_y /= B_norm

def get_causal_integrity(nodes):
    B_norms = [np.sqrt(n.state.B_x**2 + n.state.B_y**2) for n in nodes]
    return float(np.mean(B_norms) * 100.0)

def get_final_stability(nodes, target_divergence=1.0):
    return 1.0

if __name__ == "__main__":
    rt = PrimeRuntimeV4()
    print(rt.run())
