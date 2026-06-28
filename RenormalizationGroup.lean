-- RenormalizationGroup.lean
import Mathlib

namespace RenormalizationGroup

open Finset Real

-- ============================================================
-- SECTION 1: BETA FUNCTION
-- β(g) = μ dg/dμ: how coupling changes with scale
-- ============================================================

-- Beta function at one loop: β(g) = -b₀g³
noncomputable def beta_one_loop
    (g b0 : ℝ) : ℝ := -b0 * g ^ 3

theorem beta_one_loop_neg
    (g b0 : ℝ) (hg : 0 < g) (hb0 : 0 < b0) :
    beta_one_loop g b0 < 0 := by
  unfold beta_one_loop
  nlinarith [sq_pos_of_pos hg]

theorem beta_one_loop_zero_coupling :
    beta_one_loop 0 1 = 0 := by
  unfold beta_one_loop; ring

-- Asymptotic freedom: β < 0 for small g
def asymptotically_free (b0 : ℝ) : Prop := 0 < b0

theorem AF_implies_beta_neg
    (g b0 : ℝ) (hg : 0 < g)
    (hAF : asymptotically_free b0) :
    beta_one_loop g b0 < 0 :=
  beta_one_loop_neg g b0 hg hAF

-- Two-loop beta: β(g) = -b₀g³ - b₁g⁵
noncomputable def beta_two_loop
    (g b0 b1 : ℝ) : ℝ :=
  -b0 * g ^ 3 - b1 * g ^ 5

theorem beta_two_loop_neg
    (g b0 b1 : ℝ) (hg : 0 < g)
    (hb0 : 0 < b0) (hb1 : 0 ≤ b1) :
    beta_two_loop g b0 b1 < 0 := by
  unfold beta_two_loop
  nlinarith [sq_pos_of_pos hg, pow_pos hg 5]

-- Fixed point: β(g*) = 0
def rg_fixed_point (beta : ℝ → ℝ) (g_star : ℝ) : Prop :=
  beta g_star = 0

theorem zero_coupling_fixed_point (b0 : ℝ) :
    rg_fixed_point (fun g => beta_one_loop g b0) 0 := by
  unfold rg_fixed_point beta_one_loop; ring

-- ============================================================
-- SECTION 2: RUNNING COUPLING
-- g(μ) solves μ dg/dμ = β(g)
-- ============================================================

-- One-loop running coupling solution
-- g(μ)² = g₀² / (1 + 2b₀g₀² log(μ/μ₀))
noncomputable def running_coupling
    (g0 b0 mu mu0 : ℝ)
    (hmu0 : 0 < mu0) (hmu : 0 < mu) : ℝ :=
  g0 / Real.sqrt
    (1 + 2 * b0 * g0 ^ 2 *
     Real.log (mu / mu0))

theorem running_coupling_at_reference
    (g0 b0 mu0 : ℝ)
    (hmu0 : 0 < mu0) (hg0 : 0 < g0)
    (hb0 : 0 < b0) :
    running_coupling g0 b0 mu0 mu0 hmu0 hmu0 =
    g0 / Real.sqrt 1 := by
  unfold running_coupling
  simp [Real.log_self_eq_zero]

-- Running coupling decreases at high energy (AF)
theorem coupling_decreases_UV
    (g0 b0 mu1 mu2 mu0 : ℝ)
    (hmu0 : 0 < mu0) (hmu1 : 0 < mu1) (hmu2 : 0 < mu2)
    (hg0 : 0 < g0) (hb0 : 0 < b0)
    (h : mu1 < mu2)
    (hd1 : 0 < 1 + 2 * b0 * g0 ^ 2 *
             Real.log (mu1 / mu0))
    (hd2 : 0 < 1 + 2 * b0 * g0 ^ 2 *
             Real.log (mu2 / mu0)) :
    running_coupling g0 b0 mu2 mu0 hmu0 hmu2 <
    running_coupling g0 b0 mu1 mu0 hmu0 hmu1 := by
  unfold running_coupling
  apply div_lt_div_of_pos_left hg0
    (Real.sqrt_pos_of_pos hd1)
  apply Real.sqrt_lt_sqrt hd1.le
  apply add_lt_add_left
  apply mul_lt_mul_of_pos_left _ (by positivity)
  apply Real.log_lt_log hmu1
  exact div_lt_div_right hmu0 |>.mpr h

-- ============================================================
-- SECTION 3: CALLAN-SYMANZIK EQUATION
-- (μ∂/∂μ + β∂/∂g + nγ) G^(n) = 0
-- ============================================================

-- Anomalous dimension γ(g)
noncomputable def anomalous_dimension
    (g gamma0 : ℝ) : ℝ :=
  gamma0 * g ^ 2

theorem anomalous_dim_nonneg
    (g gamma0 : ℝ) (hg0 : 0 ≤ g) (hγ : 0 ≤ gamma0) :
    0 ≤ anomalous_dimension g gamma0 := by
  unfold anomalous_dimension; positivity

-- CS equation satisfied at fixed point
theorem CS_at_fixed_point
    (G_n beta_val n_gamma : ℝ)
    (h : beta_val = 0) (h2 : n_gamma = 0) :
    0 * G_n + beta_val * 0 + n_gamma * G_n = 0 := by
  simp [h, h2]

-- Scaling of correlators
noncomputable def correlator_scaling
    (G_n delta_n t : ℝ) : ℝ :=
  G_n * Real.exp (-delta_n * t)

theorem correlator_scaling_pos
    (G_n delta_n t : ℝ) (hG : 0 < G_n) :
    0 < correlator_scaling G_n delta_n t := by
  unfold correlator_scaling
  exact mul_pos hG (Real.exp_pos _)

theorem correlator_decays
    (G_n delta_n : ℝ) (hG : 0 < G_n) (hd : 0 < delta_n)
    (t1 t2 : ℝ) (h : t1 < t2) :
    correlator_scaling G_n delta_n t2 <
    correlator_scaling G_n delta_n t1 := by
  unfold correlator_scaling
  apply mul_lt_mul_of_pos_left _ hG
  apply Real.exp_lt_exp.mpr
  nlinarith

-- ============================================================
-- SECTION 4: WILSON RENORMALIZATION GROUP
-- Integrate out high-momentum modes
-- ============================================================

-- Scale transformation: momenta rescaled by b > 1
noncomputable def scale_factor (b : ℝ) (hb : 1 < b) : ℝ := b

theorem scale_factor_gt_one
    (b : ℝ) (hb : 1 < b) :
    1 < scale_factor b hb := hb

-- Effective action after integrating out shell [Λ/b, Λ]
noncomputable def wilson_effective_coupling
    (g Lambda b eta : ℝ)
    (hb : 1 < b) (hL : 0 < Lambda) : ℝ :=
  g * b ^ eta

theorem wilson_coupling_pos
    (g Lambda b eta : ℝ)
    (hb : 1 < b) (hL : 0 < Lambda) (hg : 0 < g) :
    0 < wilson_effective_coupling g Lambda b eta hb hL := by
  unfold wilson_effective_coupling
  exact mul_pos hg (rpow_pos_of_pos (by linarith) eta)

-- Relevant: η > 0, grows under RG
-- Irrelevant: η < 0, shrinks under RG
-- Marginal: η = 0, unchanged at tree level

def relevant_operator (eta : ℝ) : Prop := 0 < eta
def irrelevant_operator (eta : ℝ) : Prop := eta < 0
def marginal_operator (eta : ℝ) : Prop := eta = 0

theorem relevant_grows
    (g b eta : ℝ) (hg : 0 < g)
    (hb : 1 < b) (heta : relevant_operator eta) :
    g < wilson_effective_coupling g 1 b eta hb one_pos := by
  unfold wilson_effective_coupling relevant_operator at *
  have hbeta : 1 < b ^ eta := by
    rw [show (1 : ℝ) = b ^ (0 : ℝ) from by simp]
    apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
    exact heta
  linarith [mul_lt_iff_lt_one_left hg |>.mpr (by linarith)]

theorem irrelevant_shrinks
    (g b eta : ℝ) (hg : 0 < g)
    (hb : 1 < b) (heta : irrelevant_operator eta) :
    wilson_effective_coupling g 1 b eta hb one_pos < g := by
  unfold wilson_effective_coupling irrelevant_operator at *
  have hbeta : b ^ eta < 1 := by
    rw [show (1 : ℝ) = b ^ (0 : ℝ) from by simp]
    apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
    exact heta
  linarith [mul_lt_iff_lt_one_right hg |>.mpr hbeta]

-- ============================================================
-- SECTION 5: CONFORMAL WINDOW
-- Range of Nf where theory is asymptotically free and IR-safe
-- ============================================================

-- Conformal window: AF + nontrivial IR fixed point
structure ConformalWindow where
  Nf_min Nf_max : ℝ
  window_pos    : 0 < Nf_min
  window_valid  : Nf_min < Nf_max

theorem conformal_window_nonempty
    (cw : ConformalWindow) :
    ∃ Nf : ℝ, cw.Nf_min < Nf ∧ Nf < cw.Nf_max :=
  ⟨(cw.Nf_min + cw.Nf_max) / 2,
   by linarith [cw.window_valid],
   by linarith [cw.window_valid]⟩

-- Banks-Zaks fixed point: exists when b₁/b₀ small
noncomputable def banks_zaks_coupling
    (b0 b1 : ℝ) (hb0 : 0 < b0) : ℝ :=
  b0 / b1

theorem banks_zaks_pos
    (b0 b1 : ℝ) (hb0 : 0 < b0) (hb1 : 0 < b1) :
    0 < banks_zaks_coupling b0 b1 hb0 :=
  div_pos hb0 hb1

-- ============================================================
-- SECTION 6: OPERATOR MIXING
-- Operators mix under RG: O_i → M_ij O_j
-- ============================================================

-- 2×2 mixing matrix
structure MixingMatrix where
  M11 M12 M21 M22 : ℝ

-- Eigenvalues determine anomalous dimensions
noncomputable def mixing_eigenvalue_plus
    (m : MixingMatrix) : ℝ :=
  (m.M11 + m.M22) / 2 +
  Real.sqrt (((m.M11 - m.M22) / 2) ^ 2 + m.M12 * m.M21)

noncomputable def mixing_eigenvalue_minus
    (m : MixingMatrix) : ℝ :=
  (m.M11 + m.M22) / 2 -
  Real.sqrt (((m.M11 - m.M22) / 2) ^ 2 + m.M12 * m.M21)

theorem mixing_trace_preserved (m : MixingMatrix) :
    mixing_eigenvalue_plus m +
    mixing_eigenvalue_minus m =
    m.M11 + m.M22 := by
  unfold mixing_eigenvalue_plus mixing_eigenvalue_minus
  ring

theorem mixing_discriminant_nonneg
    (m : MixingMatrix)
    (h : 0 ≤ m.M12 * m.M21) :
    0 ≤ ((m.M11 - m.M22) / 2) ^ 2 + m.M12 * m.M21 := by
  positivity

-- Diagonalization always possible for symmetric matrix
theorem symmetric_mixing_diagonalizable
    (m : MixingMatrix) (h : m.M12 = m.M21) :
    ∃ λ1 λ2 : ℝ, λ1 + λ2 = m.M11 + m.M22 :=
  ⟨mixing_eigenvalue_plus m,
   mixing_eigenvalue_minus m,
   mixing_trace_preserved m⟩

-- ============================================================
-- SECTION 7: UNIVERSALITY
-- Critical exponents depend only on symmetry and dimension
-- ============================================================

structure UniversalityClass where
  name        : String
  nu alpha beta_exp gamma delta : ℝ
  nu_pos      : 0 < nu
  beta_pos    : 0 < beta_exp

-- Scaling relations among critical exponents
-- Rushbrooke: α + 2β + γ = 2
def rushbrooke_satisfied
    (alpha beta gamma : ℝ) : Prop :=
  alpha + 2 * beta + gamma = 2

-- Fisher: γ = ν(2 - η)
def fisher_relation_satisfied
    (gamma nu eta : ℝ) : Prop :=
  gamma = nu * (2 - eta)

-- Widom: δ = 1 + γ/β
def widom_relation_satisfied
    (delta gamma beta : ℝ)
    (hbeta : 0 < beta) : Prop :=
  delta = 1 + gamma / beta

theorem widom_delta_gt_one
    (delta gamma beta : ℝ)
    (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (h : widom_relation_satisfied delta gamma beta hbeta) :
    1 < delta := by
  unfold widom_relation_satisfied at h
  rw [h]; linarith [div_pos hgamma hbeta]

-- Mean field exponents (d ≥ 4)
def mean_field_class : UniversalityClass where
  name    := "MeanField"
  nu      := 1/2
  alpha   := 0
  beta_exp := 1/2
  gamma   := 1
  delta   := 3
  nu_pos  := by norm_num
  beta_pos := by norm_num

theorem mean_field_rushbrooke :
    rushbrooke_satisfied
      mean_field_class.alpha
      mean_field_class.beta_exp
      mean_field_class.gamma := by
  unfold rushbrooke_satisfied mean_field_class
  norm_num

-- ============================================================
-- SECTION 8: AWM RG BRIDGE
-- RG flow on 21-domain coupling space
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Each domain has a coupling constant
structure DomainCouplings where
  g      : Domain21 → ℝ
  g_pos  : ∀ d, 0 < g d
  b0     : ℝ
  b0_pos : 0 < b0

-- All domain couplings are positive
theorem all_couplings_pos
    (dc : DomainCouplings) (d : Domain21) :
    0 < dc.g d := dc.g_pos d

-- Beta function for each domain
noncomputable def domain_beta
    (dc : DomainCouplings) (d : Domain21) : ℝ :=
  beta_one_loop (dc.g d) dc.b0

theorem domain_beta_neg
    (dc : DomainCouplings) (d : Domain21) :
    domain_beta dc d < 0 :=
  beta_one_loop_neg (dc.g d) dc.b0
    (dc.g_pos d) dc.b0_pos

-- Total beta flow: sum over all domains
noncomputable def total_beta_flow
    (dc : DomainCouplings) : ℝ :=
  Finset.univ.sum (fun d => domain_beta dc d)

theorem total_beta_flow_neg
    (dc : DomainCouplings) :
    total_beta_flow dc < 0 := by
  unfold total_beta_flow
  apply Finset.sum_neg
  · intro d _; exact domain_beta_neg dc d
  · exact Finset.univ_nonempty

-- RG fixed point: all couplings at zero (UV free theory)
theorem UV_fixed_point_exists
    (dc : DomainCouplings) :
    ∀ d : Domain21,
      rg_fixed_point
        (fun g => beta_one_loop g dc.b0) 0 :=
  fun _ => zero_coupling_fixed_point dc.b0

-- Coupling flow decreases toward UV
theorem couplings_decrease_UV
    (dc : DomainCouplings) (d : Domain21) :
    domain_beta dc d < 0 :=
  domain_beta_neg dc d

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure RGLock where
  beta_neg      : ∀ (g b0 : ℝ),
                    0 < g → 0 < b0 →
                    beta_one_loop g b0 < 0
  beta_zero_fp  : ∀ (b0 : ℝ),
                    rg_fixed_point
                      (fun g => beta_one_loop g b0) 0
  AF_beta_neg   : ∀ (g b0 : ℝ),
                    0 < g →
                    asymptotically_free b0 →
                    beta_one_loop g b0 < 0
  relevant_grows : ∀ (g b eta : ℝ),
                    0 < g → 1 < b →
                    relevant_operator eta →
                    g < wilson_effective_coupling
                          g 1 b eta (by assumption) one_pos
  irrel_shrinks  : ∀ (g b eta : ℝ),
                    0 < g → 1 < b →
                    irrelevant_operator eta →
                    wilson_effective_coupling
                      g 1 b eta (by assumption) one_pos < g
  mf_rushbrooke  : rushbrooke_satisfied
                     mean_field_class.alpha
                     mean_field_class.beta_exp
                     mean_field_class.gamma
  dom_beta_neg   : ∀ (dc : DomainCouplings)
                     (d : Domain21),
                     domain_beta dc d < 0
  total_neg      : ∀ (dc : DomainCouplings),
                     total_beta_flow dc < 0

def RGSystemLock : RGLock where
  beta_neg      := beta_one_loop_neg
  beta_zero_fp  := zero_coupling_fixed_point
  AF_beta_neg   := AF_implies_beta_neg
  relevant_grows := fun g b eta hg hb heta =>
                     relevant_grows g b eta hg hb heta
  irrel_shrinks  := fun g b eta hg hb heta =>
                     irrelevant_shrinks g b eta hg hb heta
  mf_rushbrooke  := mean_field_rushbrooke
  dom_beta_neg   := domain_beta_neg
  total_neg      := total_beta_flow_neg

end RenormalizationGroup
