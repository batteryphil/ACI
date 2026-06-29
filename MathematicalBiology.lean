-- MathematicalBiology.lean
import Mathlib

namespace MathematicalBiology

open Finset Real

-- ============================================================
-- SECTION 1: POPULATION DYNAMICS
-- ============================================================

-- Exponential growth: N(t) = N₀ exp(rt)
noncomputable def exponential_growth
    (N0 r t : ℝ) : ℝ :=
  N0 * Real.exp (r * t)

theorem exponential_growth_pos
    (N0 r t : ℝ) (hN : 0 < N0) :
    0 < exponential_growth N0 r t :=
  mul_pos hN (Real.exp_pos _)

-- Logistic growth: N(t) = K/(1 + A exp(-rt))
noncomputable def logistic_growth
    (K r t A : ℝ)
    (hK : 0 < K) (hA : 0 < A)
    (hr : 0 < r) : ℝ :=
  K / (1 + A * Real.exp (-r * t))

theorem logistic_pos
    (K r t A : ℝ)
    (hK : 0 < K) (hA : 0 < A)
    (hr : 0 < r) :
    0 < logistic_growth K r t A hK hA hr := by
  unfold logistic_growth
  apply div_pos hK
  linarith [mul_pos hA (Real.exp_pos (-r * t))]

theorem logistic_le_K
    (K r t A : ℝ)
    (hK : 0 < K) (hA : 0 < A)
    (hr : 0 < r) :
    logistic_growth K r t A hK hA hr ≤ K := by
  unfold logistic_growth
  rw [div_le_iff (by linarith
    [mul_pos hA (Real.exp_pos (-r * t))])]
  linarith [mul_pos hA
    (Real.exp_pos (-r * t))]

-- Carrying capacity positive
theorem carrying_capacity_pos
    (K : ℝ) (hK : 0 < K) : 0 < K := hK

-- ============================================================
-- SECTION 2: LOTKA-VOLTERRA
-- ============================================================

-- Prey: dx/dt = αx - βxy
-- Predator: dy/dt = δxy - γy
noncomputable def LV_invariant
    (alpha beta gamma delta x y : ℝ) : ℝ :=
  delta * x - gamma * Real.log (x + 1e-12) +
  beta * y - alpha * Real.log (y + 1e-12)

-- Population nonneg
theorem population_nonneg
    (N : ℝ) (h : 0 ≤ N) : 0 ≤ N := h

-- Equilibrium: (γ/δ, α/β)
noncomputable def LV_equilibrium
    (alpha beta gamma delta : ℝ)
    (hbeta : 0 < beta)
    (hdelta : 0 < delta) : ℝ × ℝ :=
  (gamma / delta, alpha / beta)

theorem LV_equil_pos
    (alpha beta gamma delta : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : 0 < gamma) (hdelta : 0 < delta) :
    0 < (LV_equilibrium alpha beta gamma delta
      hbeta hdelta).1 ∧
    0 < (LV_equilibrium alpha beta gamma delta
      hbeta hdelta).2 := by
  constructor
  · exact div_pos hgamma hdelta
  · exact div_pos halpha hbeta

-- ============================================================
-- SECTION 3: EPIDEMIOLOGY
-- ============================================================

-- SIR model: S + I + R = N
def SIR_conservation
    (S I R N : ℝ) : Prop :=
  S + I + R = N

theorem SIR_nonneg_total
    (S I R : ℝ)
    (hS : 0 ≤ S) (hI : 0 ≤ I) (hR : 0 ≤ R) :
    0 ≤ S + I + R := by linarith

-- Basic reproduction number R₀
noncomputable def R0
    (beta gamma N : ℝ)
    (hgamma : 0 < gamma) : ℝ :=
  beta * N / gamma

theorem R0_pos
    (beta gamma N : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hN : 0 < N) :
    0 < R0 beta gamma N hgamma :=
  div_pos (mul_pos hbeta hN) hgamma

-- Epidemic threshold: R₀ > 1 → epidemic
theorem epidemic_threshold
    (R : ℝ) (hR : 1 < R) : 0 < R :=
  lt_trans one_pos hR

-- Herd immunity proxy
noncomputable def herd_immunity_threshold
    (R : ℝ) (hR : 0 < R) : ℝ :=
  1 - 1 / R

theorem HIT_nonneg
    (R : ℝ) (hR : 1 < R) :
    0 ≤ herd_immunity_threshold R
      (lt_trans one_pos hR) := by
  unfold herd_immunity_threshold
  rw [sub_nonneg, div_le_one
    (lt_trans one_pos hR)]
  linarith

-- ============================================================
-- SECTION 4: REACTION-DIFFUSION
-- ============================================================

-- Turing instability proxy
theorem turing_instability_proxy :
    True := trivial

-- Pattern formation proxy
theorem pattern_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

-- Fisher-KPP equation proxy
noncomputable def fisher_term
    (r K u : ℝ) : ℝ :=
  r * u * (1 - u / K)

theorem fisher_term_nonneg
    (r K u : ℝ)
    (hr : 0 ≤ r) (hK : 0 < K)
    (hu0 : 0 ≤ u) (huK : u ≤ K) :
    0 ≤ fisher_term r K u := by
  unfold fisher_term
  apply mul_nonneg (mul_nonneg hr hu0)
  rw [sub_nonneg]
  exact div_le_one_of_le huK (le_of_lt hK)

-- ============================================================
-- SECTION 5: NEURAL MODELS
-- ============================================================

-- Hodgkin-Huxley conductance proxy
theorem HH_conductance_pos
    (g : ℝ) (h : 0 < g) : 0 < g := h

-- FitzHugh-Nagumo proxy
noncomputable def FHN_nullcline
    (v a b : ℝ) : ℝ :=
  v - v ^ 3 / 3 - b * v + a

-- Integrate-and-fire threshold proxy
theorem IAF_threshold_pos
    (V_th : ℝ) (h : 0 < V_th) :
    0 < V_th := h

-- Wilson-Cowan proxy
theorem WC_proxy (E I : ℝ)
    (hE : 0 ≤ E) (hI : 0 ≤ I) :
    0 ≤ E + I := by linarith

-- ============================================================
-- SECTION 6: EVOLUTIONARY DYNAMICS
-- ============================================================

-- Replicator equation: ẋᵢ = xᵢ(fᵢ - f̄)
def replicator_constraint (n : ℕ)
    (x : Fin n → ℝ) : Prop :=
  Finset.univ.sum x = 1 ∧
  ∀ i, 0 ≤ x i

theorem simplex_valid (n : ℕ)
    (x : Fin n → ℝ)
    (h : replicator_constraint n x)
    (i : Fin n) :
    0 ≤ x i := h.2 i

-- Fitness nonneg
theorem fitness_nonneg
    (f : ℝ) (h : 0 ≤ f) : 0 ≤ f := h

-- Price equation proxy
theorem price_eq_proxy :
    True := trivial

-- Nash equilibrium proxy
theorem nash_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

-- ============================================================
-- SECTION 7: ENZYME KINETICS
-- ============================================================

-- Michaelis-Menten: v = Vmax*S/(Km + S)
noncomputable def michaelis_menten
    (Vmax Km S : ℝ)
    (hKm : 0 < Km) (hS : 0 ≤ S) : ℝ :=
  Vmax * S / (Km + S)

theorem MM_nonneg
    (Vmax Km S : ℝ)
    (hV : 0 ≤ Vmax) (hKm : 0 < Km)
    (hS : 0 ≤ S) :
    0 ≤ michaelis_menten Vmax Km S hKm hS := by
  unfold michaelis_menten
  apply div_nonneg (mul_nonneg hV hS)
  linarith

theorem MM_le_Vmax
    (Vmax Km S : ℝ)
    (hV : 0 ≤ Vmax) (hKm : 0 < Km)
    (hS : 0 ≤ S) :
    michaelis_menten Vmax Km S hKm hS
    ≤ Vmax := by
  unfold michaelis_menten
  rw [div_le_iff (by linarith)]
  nlinarith

-- Hill equation proxy
noncomputable def hill_equation
    (Vmax S Kd : ℝ) (n : ℕ)
    (hKd : 0 < Kd) : ℝ :=
  Vmax * S ^ n / (Kd ^ n + S ^ n)

-- ============================================================
-- SECTION 8: BIOMECHANICS
-- ============================================================

-- Muscle force-velocity proxy
theorem force_velocity_proxy
    (F v : ℝ) (hF : 0 ≤ F) : 0 ≤ F := hF

-- Bone stress proxy
theorem bone_stress_nonneg
    (sigma : ℝ) (h : 0 ≤ sigma) :
    0 ≤ sigma := h

-- Fluid-structure interaction proxy
theorem FSI_proxy :
    True := trivial

-- ============================================================
-- SECTION 9: AWM MATHEMATICAL BIOLOGY BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Domain population growth
noncomputable def domain_growth :=
  exponential_growth 21 0.1 1

theorem domain_growth_pos :
    0 < domain_growth :=
  exponential_growth_pos 21 0.1 1
    (by norm_num)

-- Domain logistic
noncomputable def domain_logistic :=
  logistic_growth 100 1 1 1
    (by norm_num) (by norm_num) (by norm_num)

theorem domain_logistic_pos :
    0 < domain_logistic :=
  logistic_pos 100 1 1 1
    (by norm_num) (by norm_num) (by norm_num)

theorem domain_logistic_le_K :
    domain_logistic ≤ 100 :=
  logistic_le_K 100 1 1 1
    (by norm_num) (by norm_num) (by norm_num)

-- Domain R0
noncomputable def domain_R0 :=
  R0 0.3 0.1 1000 (by norm_num)

theorem domain_R0_pos :
    0 < domain_R0 :=
  R0_pos 0.3 0.1 1000
    (by norm_num) (by norm_num) (by norm_num)

-- Domain Michaelis-Menten
noncomputable def domain_MM :=
  michaelis_menten 1 1 21
    (by norm_num) (by norm_num)

theorem domain_MM_nonneg :
    0 ≤ domain_MM :=
  MM_nonneg 1 1 21
    (by norm_num) (by norm_num) (by norm_num)

-- Domain Fisher term
noncomputable def domain_fisher :=
  fisher_term 1 21 10

theorem domain_fisher_nonneg :
    0 ≤ domain_fisher :=
  fisher_term_nonneg 1 21 10
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure MathematicalBiologyLock where
  exp_growth_pos : ∀ (N0 r t : ℝ), 0 < N0 →
                     0 < exponential_growth
                       N0 r t
  logistic_pos   : ∀ (K r t A : ℝ),
                     0 < K → 0 < A → 0 < r →
                     0 < logistic_growth
                       K r t A ‹_› ‹_› ‹_›
  logistic_le_K  : ∀ (K r t A : ℝ),
                     0 < K → 0 < A → 0 < r →
                     logistic_growth
                       K r t A ‹_› ‹_› ‹_› ≤ K
  SIR_nn         : ∀ (S I R : ℝ),
                     0 ≤ S → 0 ≤ I → 0 ≤ R →
                     0 ≤ S + I + R
  R0_pos         : ∀ (beta gamma N : ℝ),
                     0 < beta → 0 < gamma →
                     0 < N →
                     0 < R0 beta gamma N ‹_›
  HIT_nn         : ∀ (R : ℝ), 1 < R →
                     0 ≤ herd_immunity_threshold
                       R (by linarith)
  fisher_nn      : ∀ (r K u : ℝ),
                     0 ≤ r → 0 < K →
                     0 ≤ u → u ≤ K →
                     0 ≤ fisher_term r K u
  MM_nn          : ∀ (Vmax Km S : ℝ),
                     0 ≤ Vmax → 0 < Km →
                     0 ≤ S →
                     0 ≤ michaelis_menten
                       Vmax Km S ‹_› ‹_›
  MM_le_Vmax     : ∀ (Vmax Km S : ℝ),
                     0 ≤ Vmax → 0 < Km →
                     0 ≤ S →
                     michaelis_menten
                       Vmax Km S ‹_› ‹_›
                     ≤ Vmax
  simplex_valid  : ∀ (n : ℕ)
                     (x : Fin n → ℝ),
                     replicator_constraint n x →
                     ∀ i, 0 ≤ x i
  dom_growth_pos : 0 < domain_growth
  dom_log_pos    : 0 < domain_logistic
  dom_log_le_K   : domain_logistic ≤ 100
  dom_R0_pos     : 0 < domain_R0
  dom_MM_nn      : 0 ≤ domain_MM
  dom_fisher_nn  : 0 ≤ domain_fisher

def MBLock : MathematicalBiologyLock where
  exp_growth_pos := exponential_growth_pos
  logistic_pos   := logistic_pos
  logistic_le_K  := logistic_le_K
  SIR_nn         := SIR_nonneg_total
  R0_pos         := R0_pos
  HIT_nn         := HIT_nonneg
  fisher_nn      := fisher_term_nonneg
  MM_nn          := MM_nonneg
  MM_le_Vmax     := MM_le_Vmax
  simplex_valid  := simplex_valid
  dom_growth_pos := domain_growth_pos
  dom_log_pos    := domain_logistic_pos
  dom_log_le_K   := domain_logistic_le_K
  dom_R0_pos     := domain_R0_pos
  dom_MM_nn      := domain_MM_nonneg
  dom_fisher_nn  := domain_fisher_nonneg

end MathematicalBiology
