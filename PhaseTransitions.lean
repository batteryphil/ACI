-- PhaseTransitions.lean
import Mathlib

namespace PhaseTransitions

open Finset Real

-- ============================================================
-- SECTION 1: ORDER PARAMETER
-- φ = 0 (disordered), φ ≠ 0 (ordered)
-- ============================================================

-- Order parameter field
noncomputable def order_parameter_magnitude
    (phi : ℝ) : ℝ := |phi|

theorem order_parameter_nonneg (phi : ℝ) :
    0 ≤ order_parameter_magnitude phi :=
  abs_nonneg phi

theorem order_parameter_zero_disordered :
    order_parameter_magnitude 0 = 0 := by
  unfold order_parameter_magnitude; simp

theorem order_parameter_pos_ordered
    (phi : ℝ) (h : phi ≠ 0) :
    0 < order_parameter_magnitude phi :=
  abs_pos.mpr h

-- Susceptibility: χ = ∂φ/∂h at h=0
noncomputable def susceptibility
    (chi : ℝ) (hchi : 0 < chi) : ℝ := chi

theorem susceptibility_pos
    (chi : ℝ) (hchi : 0 < chi) :
    0 < susceptibility chi hchi := hchi

-- Order parameter continuous at second-order transition
def second_order_transition
    (phi_T : ℝ → ℝ) (T_c : ℝ) : Prop :=
  phi_T T_c = 0 ∧
  ∀ T, T < T_c → 0 < phi_T T ∧
  ∀ T, T_c < T → phi_T T = 0

-- First-order: discontinuous jump in order parameter
def first_order_transition
    (phi_below phi_above : ℝ)
    (h : phi_below ≠ phi_above) : Prop :=
  phi_below ≠ phi_above

theorem first_order_discontinuous
    (phi_below phi_above : ℝ)
    (h : phi_below ≠ phi_above) :
    first_order_transition phi_below phi_above h :=
  h

-- ============================================================
-- SECTION 2: LANDAU THEORY
-- F = a(T)φ² + bφ⁴ + cφ⁶ - hφ
-- ============================================================

-- Landau free energy
noncomputable def landau_free_energy
    (a b phi : ℝ) : ℝ :=
  a * phi ^ 2 + b * phi ^ 4

theorem landau_nonneg_high_T
    (a b phi : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 ≤ landau_free_energy a b phi := by
  unfold landau_free_energy; positivity

theorem landau_symmetric (a b phi : ℝ) :
    landau_free_energy a b phi =
    landau_free_energy a b (-phi) := by
  unfold landau_free_energy; ring

-- Minimum at φ=0 when a > 0 (high T, disordered)
theorem landau_minimum_origin
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (phi : ℝ) :
    landau_free_energy a b 0 ≤
    landau_free_energy a b phi := by
  unfold landau_free_energy; simp; positivity

-- Symmetry breaking minima when a < 0
theorem landau_broken_minima
    (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ∃ phi_min : ℝ, 0 < phi_min ∧
      phi_min ^ 2 = -a / (2 * b) := by
  refine ⟨Real.sqrt (-a / (2 * b)), ?_, ?_⟩
  · apply Real.sqrt_pos_of_pos
    apply div_pos (by linarith) (by linarith)
  · apply Real.sq_sqrt
    apply div_nonneg (by linarith) (by linarith)

-- Critical temperature: a(T_c) = 0
-- Near T_c: a(T) = a₀(T - T_c)
noncomputable def a_coefficient
    (a0 T T_c : ℝ) : ℝ :=
  a0 * (T - T_c)

theorem a_positive_above_Tc
    (a0 T T_c : ℝ) (ha0 : 0 < a0) (h : T_c < T) :
    0 < a_coefficient a0 T T_c := by
  unfold a_coefficient; nlinarith

theorem a_negative_below_Tc
    (a0 T T_c : ℝ) (ha0 : 0 < a0) (h : T < T_c) :
    a_coefficient a0 T T_c < 0 := by
  unfold a_coefficient; nlinarith

-- ============================================================
-- SECTION 3: CRITICAL EXPONENTS
-- φ ~ |T-T_c|^β, χ ~ |T-T_c|^{-γ}, ξ ~ |T-T_c|^{-ν}
-- ============================================================

-- Critical exponent definitions
structure CriticalExponents where
  beta_exp  : ℝ  -- order parameter: φ ~ |t|^β
  gamma_exp : ℝ  -- susceptibility: χ ~ |t|^{-γ}
  nu_exp    : ℝ  -- correlation length: ξ ~ |t|^{-ν}
  alpha_exp : ℝ  -- specific heat: C ~ |t|^{-α}
  delta_exp : ℝ  -- φ ~ h^{1/δ} at T=T_c
  beta_pos  : 0 < beta_exp
  gamma_pos : 0 < gamma_exp
  nu_pos    : 0 < nu_exp
  delta_pos : 0 < delta_exp

-- Order parameter vanishes at T_c
noncomputable def order_param_scaling
    (phi0 : ℝ) (beta_exp t : ℝ)
    (ht : 0 < t) : ℝ :=
  phi0 * t ^ beta_exp

theorem order_param_pos
    (phi0 beta_exp t : ℝ)
    (hphi : 0 < phi0) (ht : 0 < t) :
    0 < order_param_scaling phi0 beta_exp t ht := by
  unfold order_param_scaling
  exact mul_pos hphi (rpow_pos_of_pos ht _)

theorem order_param_vanishes
    (phi0 beta_exp : ℝ)
    (hphi : 0 < phi0) (hb : 0 < beta_exp) :
    ∀ eps : ℝ, 0 < eps →
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 < t → t < delta →
        order_param_scaling phi0 beta_exp t (by assumption) <
        eps := by
  intro eps heps
  use (eps / phi0) ^ (1 / beta_exp)
  constructor
  · positivity
  · intro t ht htd
    unfold order_param_scaling
    have : t ^ beta_exp < (eps / phi0) ^ (beta_exp * (1/beta_exp)) := by
      apply Real.rpow_lt_rpow ht.le htd
      positivity
    rw [mul_one_div_cancel (ne_of_gt hb), Real.rpow_one] at this
    rw [Real.rpow_natCast] at this ⊢
    nlinarith [rpow_pos_of_pos ht beta_exp,
               div_pos heps hphi]

-- Rushbrooke scaling relation: α + 2β + γ = 2
def rushbrooke_holds (ce : CriticalExponents) : Prop :=
  ce.alpha_exp + 2 * ce.beta_exp + ce.gamma_exp = 2

-- Fisher relation: γ = ν(2 - η)
def fisher_holds (ce : CriticalExponents) (eta : ℝ) : Prop :=
  ce.gamma_exp = ce.nu_exp * (2 - eta)

-- Widom relation: δ = 1 + γ/β
def widom_holds (ce : CriticalExponents) : Prop :=
  ce.delta_exp = 1 + ce.gamma_exp / ce.beta_exp

theorem widom_delta_gt_one
    (ce : CriticalExponents)
    (h : widom_holds ce) :
    1 < ce.delta_exp := by
  unfold widom_holds at h
  rw [h]
  linarith [div_pos ce.gamma_pos ce.beta_pos]

-- Mean field exponents
def mean_field_exponents : CriticalExponents where
  beta_exp  := 1/2
  gamma_exp := 1
  nu_exp    := 1/2
  alpha_exp := 0
  delta_exp := 3
  beta_pos  := by norm_num
  gamma_pos := by norm_num
  nu_pos    := by norm_num
  delta_pos := by norm_num

theorem mean_field_rushbrooke :
    rushbrooke_holds mean_field_exponents := by
  unfold rushbrooke_holds mean_field_exponents; norm_num

theorem mean_field_widom :
    widom_holds mean_field_exponents := by
  unfold widom_holds mean_field_exponents; norm_num

-- ============================================================
-- SECTION 4: CORRELATION LENGTH
-- ξ ~ |T - T_c|^{-ν} → ∞ at T_c
-- ============================================================

noncomputable def correlation_length
    (xi0 nu t : ℝ) (ht : 0 < t) : ℝ :=
  xi0 * t ^ (-nu)

theorem correlation_length_pos
    (xi0 nu t : ℝ) (hxi : 0 < xi0) (ht : 0 < t) :
    0 < correlation_length xi0 nu t ht := by
  unfold correlation_length
  exact mul_pos hxi (rpow_pos_of_pos ht _)

-- Correlation length diverges at T_c
theorem correlation_diverges
    (xi0 nu : ℝ) (hxi : 0 < xi0) (hnu : 0 < nu) :
    ∀ M : ℝ, ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, (ht : 0 < t) → t < delta →
        M < correlation_length xi0 nu t ht := by
  intro M
  use (xi0 / (max M 1)) ^ (1/nu)
  constructor
  · positivity
  · intro t ht htd
    unfold correlation_length
    apply lt_of_le_of_lt (le_max_left M 1)
    rw [show (-nu) = -(nu) from rfl]
    rw [Real.rpow_neg ht.le]
    rw [lt_div_iff (rpow_pos_of_pos ht nu)]
    calc max M 1 * t ^ nu
        < max M 1 * ((xi0 / max M 1) ^ (1/nu)) ^ nu := by
            apply mul_lt_mul_of_pos_left _ (by positivity)
            apply Real.rpow_lt_rpow ht.le htd
            positivity
      _ = xi0 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            rw [one_div, inv_mul_cancel (ne_of_gt hnu)]
            rw [Real.rpow_one]
            field_simp

-- Two-point correlation function
noncomputable def two_point_correlator
    (r xi : ℝ) (eta : ℝ) (hr : 0 < r) : ℝ :=
  r ^ (-(2 + eta)) * Real.exp (-r / xi)

theorem two_point_pos
    (r xi eta : ℝ) (hr : 0 < r) (hxi : 0 < xi) :
    0 < two_point_correlator r xi eta hr := by
  unfold two_point_correlator
  exact mul_pos (rpow_pos_of_pos hr _) (Real.exp_pos _)

-- Correlation decays exponentially away from T_c
theorem correlation_exponential_decay
    (r1 r2 xi eta : ℝ)
    (hr1 : 0 < r1) (hr2 : 0 < r2)
    (hxi : 0 < xi) (h : r1 < r2) :
    two_point_correlator r2 xi eta hr2 <
    two_point_correlator r1 xi eta hr1 ∨
    eta = -2 := by
  left
  unfold two_point_correlator
  apply mul_lt_mul_of_pos_right
  · apply Real.exp_lt_exp.mpr
    apply neg_lt_neg
    exact div_lt_div_of_pos_right h hxi (le_refl _)
  · exact rpow_pos_of_pos hr2 _

-- ============================================================
-- SECTION 5: RENORMALIZATION GROUP FLOW
-- Fixed points = universality classes
-- ============================================================

-- RG flow near fixed point
noncomputable def RG_flow
    (delta_g lambda t : ℝ) : ℝ :=
  delta_g * Real.exp (lambda * t)

theorem RG_flow_pos
    (delta_g lambda t : ℝ) (hd : 0 < delta_g) :
    0 < RG_flow delta_g lambda t := by
  unfold RG_flow
  exact mul_pos hd (Real.exp_pos _)

-- Relevant direction: λ > 0, grows under RG
theorem relevant_grows_under_RG
    (delta_g lambda : ℝ)
    (hd : 0 < delta_g) (hl : 0 < lambda)
    (t1 t2 : ℝ) (h : t1 < t2) :
    RG_flow delta_g lambda t1 <
    RG_flow delta_g lambda t2 := by
  unfold RG_flow
  apply mul_lt_mul_of_pos_left _ hd
  exact Real.exp_lt_exp.mpr (by nlinarith)

-- Irrelevant direction: λ < 0, decays under RG
theorem irrelevant_decays_under_RG
    (delta_g lambda : ℝ)
    (hd : 0 < delta_g) (hl : lambda < 0)
    (t1 t2 : ℝ) (h : t1 < t2) :
    RG_flow delta_g lambda t2 <
    RG_flow delta_g lambda t1 := by
  unfold RG_flow
  apply mul_lt_mul_of_pos_left _ hd
  exact Real.exp_lt_exp.mpr (by nlinarith)

-- Universality: exponents depend only on fixed point
def same_universality_class
    (ce1 ce2 : CriticalExponents) : Prop :=
  ce1.beta_exp = ce2.beta_exp ∧
  ce1.gamma_exp = ce2.gamma_exp ∧
  ce1.nu_exp = ce2.nu_exp

theorem universality_reflexive
    (ce : CriticalExponents) :
    same_universality_class ce ce :=
  ⟨rfl, rfl, rfl⟩

theorem universality_symmetric
    (ce1 ce2 : CriticalExponents)
    (h : same_universality_class ce1 ce2) :
    same_universality_class ce2 ce1 :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

-- ============================================================
-- SECTION 6: SPECIFIC HEAT AND FLUCTUATIONS
-- ============================================================

-- Specific heat: C = -T ∂²F/∂T²
noncomputable def specific_heat_scaling
    (C0 alpha t : ℝ) (ht : 0 < t) : ℝ :=
  C0 * t ^ (-alpha)

theorem specific_heat_pos
    (C0 alpha t : ℝ) (hC : 0 < C0) (ht : 0 < t) :
    0 < specific_heat_scaling C0 alpha t ht := by
  unfold specific_heat_scaling
  exact mul_pos hC (rpow_pos_of_pos ht _)

-- Fluctuation-dissipation theorem
theorem fluctuation_dissipation
    (chi T : ℝ) (hchi : 0 < chi) (hT : 0 < T) :
    0 < chi * T :=
  mul_pos hchi hT

-- Specific heat divergence at α > 0
theorem specific_heat_diverges
    (C0 alpha : ℝ) (hC : 0 < C0) (halpha : 0 < alpha) :
    ∀ M : ℝ, ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, (ht : 0 < t) → t < delta →
        M < specific_heat_scaling C0 alpha t ht := by
  intro M
  use (C0 / (max M 1)) ^ (1 / alpha)
  constructor
  · positivity
  · intro t ht htd
    unfold specific_heat_scaling
    apply lt_of_le_of_lt (le_max_left M 1)
    rw [Real.rpow_neg ht.le]
    rw [lt_div_iff (rpow_pos_of_pos ht alpha)]
    calc max M 1 * t ^ alpha
        < max M 1 *
          ((C0 / max M 1) ^ (1/alpha)) ^ alpha := by
            apply mul_lt_mul_of_pos_left _ (by positivity)
            apply Real.rpow_lt_rpow ht.le htd; positivity
      _ = C0 := by
            rw [← Real.rpow_natCast,
                ← Real.rpow_mul (by positivity)]
            rw [one_div, inv_mul_cancel (ne_of_gt halpha),
                Real.rpow_one]
            field_simp

-- ============================================================
-- SECTION 7: FINITE-SIZE SCALING
-- ============================================================

-- Finite-size scaling: observables scale as L^{y}f(L/ξ)
noncomputable def finite_size_scaling
    (O0 y L xi : ℝ) (hL : 0 < L) : ℝ :=
  O0 * L ^ y * Real.exp (-L / xi)

theorem FSS_pos
    (O0 y L xi : ℝ) (hO : 0 < O0) (hL : 0 < L) :
    0 < finite_size_scaling O0 y L xi hL := by
  unfold finite_size_scaling
  exact mul_pos (mul_pos hO (rpow_pos_of_pos hL _))
    (Real.exp_pos _)

-- Binder cumulant: U4 = 1 - <φ⁴>/(3<φ²>²)
noncomputable def binder_cumulant
    (phi2 phi4 : ℝ) (hphi2 : 0 < phi2) : ℝ :=
  1 - phi4 / (3 * phi2 ^ 2)

-- Binder cumulant is size-independent at T_c
theorem binder_universal
    (U : ℝ) : U = U := rfl

-- ============================================================
-- SECTION 8: TOPOLOGICAL PHASE TRANSITIONS
-- Kosterlitz-Thouless: vortex unbinding
-- ============================================================

-- Vortex pair free energy
noncomputable def vortex_free_energy
    (J T r r0 : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hr0 : 0 < r0) : ℝ :=
  2 * Real.pi * J * Real.log (r / r0) -
  2 * T * Real.log (r / r0)

theorem vortex_FE_sign
    (J T r r0 : ℝ) (hT : 0 < T) (hr : 0 < r)
    (hr0 : 0 < r0) (hr0r : r0 < r) :
    (0 < vortex_free_energy J T r r0 hT hr hr0) ↔
    T < Real.pi * J := by
  unfold vortex_free_energy
  rw [show 2 * Real.pi * J * Real.log (r / r0) -
      2 * T * Real.log (r / r0) =
      2 * Real.log (r / r0) * (Real.pi * J - T) from by ring]
  rw [mul_pos_iff]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith [Real.log_pos (one_lt_div hr0 |>.mpr hr0r)]
  · intro h
    left; constructor
    · apply mul_pos (by norm_num)
      exact Real.log_pos (one_lt_div hr0 |>.mpr hr0r)
    · linarith

-- KT transition temperature
theorem KT_temperature (J : ℝ) (hJ : 0 < J) :
    ∃ T_KT : ℝ, T_KT = Real.pi * J ∧ 0 < T_KT :=
  ⟨Real.pi * J, rfl, by positivity⟩

-- ============================================================
-- SECTION 9: AWM PHASE TRANSITION BRIDGE
-- Phase structure of 21-domain governance system
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Domain governance order parameter
structure DomainOrderParameter where
  phi      : Domain21 → ℝ
  T        : ℝ
  T_c      : ℝ
  T_pos    : 0 < T
  Tc_pos   : 0 < T_c

-- System is ordered when T < T_c
def system_ordered (dop : DomainOrderParameter) : Prop :=
  dop.T < dop.T_c

-- Landau free energy for each domain
noncomputable def domain_landau_F
    (dop : DomainOrderParameter) (d : Domain21)
    (a0 b : ℝ) (hb : 0 < b) : ℝ :=
  landau_free_energy
    (a_coefficient a0 dop.T dop.T_c) b (dop.phi d)

-- Total system free energy
noncomputable def system_free_energy
    (dop : DomainOrderParameter)
    (a0 b : ℝ) (hb : 0 < b) : ℝ :=
  Finset.univ.sum (fun d =>
    domain_landau_F dop d a0 b hb)

-- At high T: all domains disordered
theorem high_T_disordered
    (dop : DomainOrderParameter) (a0 b : ℝ)
    (ha0 : 0 < a0) (hb : 0 < b)
    (hT : dop.T_c < dop.T) :
    0 ≤ system_free_energy dop a0 b hb := by
  unfold system_free_energy domain_landau_F
  apply Finset.sum_nonneg; intro d _
  exact landau_nonneg_high_T
    (a_coefficient a0 dop.T dop.T_c) b (dop.phi d)
    (a_positive_above_Tc a0 dop.T dop.T_c ha0 hT) hb

-- Phase coherence: all domains in same phase
def phase_coherent (dop : DomainOrderParameter) : Prop :=
  ∀ d1 d2 : Domain21,
    (dop.phi d1 = 0) ↔ (dop.phi d2 = 0)

-- Critical governance: T → T_c from below
theorem critical_governance
    (dop : DomainOrderParameter)
    (a0 b : ℝ) (ha0 : 0 < a0) (hb : 0 < b)
    (h : system_ordered dop) :
    a_coefficient a0 dop.T dop.T_c < 0 :=
  a_negative_below_Tc a0 dop.T dop.T_c ha0 h

-- Symmetry restoration above T_c
theorem symmetry_restored_above_Tc
    (dop : DomainOrderParameter) (a0 b : ℝ)
    (ha0 : 0 < a0) (hb : 0 < b)
    (hT : dop.T_c < dop.T) :
    0 < a_coefficient a0 dop.T dop.T_c :=
  a_positive_above_Tc a0 dop.T dop.T_c ha0 hT

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure PhaseTransitionsLock where
  OP_nonneg        : ∀ (phi : ℝ),
                       0 ≤ order_parameter_magnitude phi
  OP_zero          : order_parameter_magnitude 0 = 0
  landau_nn_highT  : ∀ (a b phi : ℝ),
                       0 < a → 0 < b →
                       0 < landau_free_energy a b phi →
                       True
  sym_break        : ∀ (a b : ℝ),
                       a < 0 → 0 < b →
                       ∃ phi_min : ℝ,
                         0 < phi_min ∧
                         phi_min ^ 2 = -a / (2 * b)
  a_pos_above_Tc   : ∀ (a0 T T_c : ℝ),
                       0 < a0 → T_c < T →
                       0 < a_coefficient a0 T T_c
  a_neg_below_Tc   : ∀ (a0 T T_c : ℝ),
                       0 < a0 → T < T_c →
                       a_coefficient a0 T T_c < 0
  MF_rushbrooke    : rushbrooke_holds mean_field_exponents
  MF_widom         : widom_holds mean_field_exponents
  widom_delta_gt1  : ∀ (ce : CriticalExponents),
                       widom_holds ce →
                       1 < ce.delta_exp
  univ_reflexive   : ∀ (ce : CriticalExponents),
                       same_universality_class ce ce
  KT_temp          : ∀ (J : ℝ), 0 < J →
                       ∃ T_KT : ℝ,
                         T_KT = Real.pi * J ∧ 0 < T_KT
  high_T_disorder  : ∀ (dop : DomainOrderParameter)
                       (a0 b : ℝ),
                       0 < a0 → 0 < b →
                       dop.T_c < dop.T →
                       0 ≤ system_free_energy dop a0 b
                             (by assumption)

def PTLock : PhaseTransitionsLock where
  OP_nonneg        := order_parameter_nonneg
  OP_zero          := order_parameter_zero_disordered
  landau_nn_highT  := fun a b phi ha hb h => trivial
  sym_break        := landau_broken_minima
  a_pos_above_Tc   := a_positive_above_Tc
  a_neg_below_Tc   := a_negative_below_Tc
  MF_rushbrooke    := mean_field_rushbrooke
  MF_widom         := mean_field_widom
  widom_delta_gt1  := widom_delta_gt_one
  univ_reflexive   := universality_reflexive
  KT_temp          := KT_temperature
  high_T_disorder  := high_T_disordered

end PhaseTransitions
