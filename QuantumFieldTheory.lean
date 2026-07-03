-- QuantumFieldTheory.lean
import Mathlib

namespace QuantumFieldTheory

open Finset Real

-- SECTION 1: CLASSICAL FIELD THEORY

noncomputable def lagrangian_density
    (phi dphi : ℝ) (m : ℝ) : ℝ :=
  (1/2) * dphi ^ 2 - (1/2) * m ^ 2 * phi ^ 2

noncomputable def action (n : ℕ)
    (L : Fin n → ℝ) : ℝ :=
  Finset.univ.sum L

theorem action_linear (n : ℕ)
    (L1 L2 : Fin n → ℝ) (c : ℝ) :
    action n (fun i => L1 i + c * L2 i) =
    action n L1 + c * action n L2 := by
  unfold action
  simp [Finset.sum_add_distrib,
        Finset.mul_sum, mul_add]
  ring

theorem EL_proxy (phi : ℝ → ℝ) :
    ∃ EOM : ℝ → ℝ, True :=
  ⟨fun _ => 0, trivial⟩

theorem noether_proxy
    (J : ℝ → ℝ) (hJ : ∀ t, 0 ≤ J t) :
    ∀ t, 0 ≤ J t := hJ

-- SECTION 2: CANONICAL QUANTIZATION

theorem commutator_bound_proxy
    (phi pi hbar : ℝ) (hh : 0 < hbar) :
    ∃ c : ℝ, c = hbar := ⟨hbar, rfl⟩

def occupation_number (n : ℕ) : ℕ := n

theorem occupation_nonneg (n : ℕ) :
    0 ≤ occupation_number n :=
  Nat.zero_le n

noncomputable def creation_norm
    (n : ℕ) : ℝ :=
  Real.sqrt (n + 1)

theorem creation_norm_pos (n : ℕ) :
    0 < creation_norm n := by
  unfold creation_norm
  apply Real.sqrt_pos_of_pos
  positivity

noncomputable def annihilation_norm
    (n : ℕ) (hn : 0 < n) : ℝ :=
  Real.sqrt n

theorem annihilation_norm_pos
    (n : ℕ) (hn : 0 < n) :
    0 < annihilation_norm n hn :=
  Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hn)

noncomputable def zero_point_energy
    (hbar omega : ℝ) : ℝ :=
  hbar * omega / 2

theorem ZPE_pos
    (hbar omega : ℝ)
    (hh : 0 < hbar) (hw : 0 < omega) :
    0 < zero_point_energy hbar omega := by
  unfold zero_point_energy
  positivity

-- SECTION 3: PATH INTEGRALS

noncomputable def euclidean_partition
    (n : ℕ) (beta : ℝ)
    (E : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i =>
    Real.exp (-beta * E i))

-- `Fintype.card_pos_iff.mp hn` needs `hn : 0 < Fintype.card (Fin n)`, but
-- the actual `hn` has type `0 < n` — not syntactically identical despite
-- propositional equality (same risk already found and fixed in
-- Thermodynamics). Rebuilt via a direct, unambiguous Finset.Nonempty
-- witness.
theorem euclidean_Z_pos (n : ℕ)
    (hn : 0 < n) (beta : ℝ)
    (E : Fin n → ℝ) :
    0 < euclidean_partition n beta E := by
  unfold euclidean_partition
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

noncomputable def propagator_proxy
    (m t : ℝ) (hm : 0 < m) : ℝ :=
  Real.exp (-m * |t|)

theorem propagator_pos
    (m t : ℝ) (hm : 0 < m) :
    0 < propagator_proxy m t hm :=
  Real.exp_pos _

theorem wick_rotation_proxy
    (t : ℝ) : ∃ tau : ℝ, tau = t := ⟨t, rfl⟩

-- SECTION 4: PERTURBATION THEORY

def coupling_small (g : ℝ) : Prop :=
  |g| < 1

noncomputable def perturbation_series
    (g : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum (fun n =>
    a n * g ^ n)

theorem perturbation_nonneg
    (g : ℝ) (hg : 0 ≤ g)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (N : ℕ) :
    0 ≤ perturbation_series g a N := by
  unfold perturbation_series
  apply Finset.sum_nonneg; intro n _
  exact mul_nonneg (ha n) (pow_nonneg hg n)

theorem dyson_series_nonneg
    (n : ℕ) : 0 ≤ (n : ℝ) :=
  Nat.cast_nonneg n

-- SECTION 5: RENORMALIZATION

noncomputable def running_coupling
    (g0 b0 mu mu0 : ℝ)
    (hmu0 : 0 < mu0) (hmu : 0 < mu)
    (hb0 : 0 < b0) : ℝ :=
  g0 / Real.sqrt (1 + 2 * b0 * g0 ^ 2 *
    Real.log (mu / mu0))

noncomputable def beta_function
    (b0 g : ℝ) : ℝ :=
  -b0 * g ^ 3

-- CONFIRMED PRE-EXISTING MATHEMATICAL ERROR (not a proof-tactic bug, the
-- same class of issue found in CodingTheory's hamming_singleton earlier
-- this session): the original hypothesis `g ≠ 0` makes the claim FALSE
-- for negative g — e.g. b0=1, g=-1 gives beta_function = 1 > 0, not < 0.
-- Every downstream call site (asymptotic_freedom_proxy, all domain_*
-- usages) passes g=1>0, so narrowing the hypothesis to 0 < g (the real
-- physics intent — asymptotic freedom for a positive coupling) breaks
-- nothing. The original proof itself was also a broken, non-typechecking
-- chain of dot-notation calls; rebuilt from scratch as a direct,
-- straightforward proof of the corrected, true statement.
theorem beta_neg_AF (b0 g : ℝ)
    (hb0 : 0 < b0) (hg : 0 < g) :
    beta_function b0 g < 0 := by
  unfold beta_function
  have hg3 : 0 < g ^ 3 := pow_pos hg 3
  nlinarith [mul_pos hb0 hg3]

theorem asymptotic_freedom_proxy
    (b0 : ℝ) (hb0 : 0 < b0) :
    beta_function b0 1 < 0 := by
  unfold beta_function
  linarith

theorem dim_reg_proxy (eps : ℝ) :
    ∃ reg : ℝ, reg = 1 / eps ∨ True :=
  ⟨0, Or.inr trivial⟩

-- SECTION 6: GAUGE THEORY

def gauge_invariant (O : ℝ → ℝ) : Prop :=
  ∀ alpha, O alpha = O 0

noncomputable def YM_action (n : ℕ)
    (F : Fin n → Fin n → ℝ) : ℝ :=
  (1/4) * Finset.univ.sum (fun mu =>
    Finset.univ.sum (fun nu =>
      F mu nu ^ 2))

theorem YM_action_nonneg (n : ℕ)
    (F : Fin n → Fin n → ℝ) :
    0 ≤ YM_action n F := by
  unfold YM_action
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg; intro mu _
  apply Finset.sum_nonneg; intro nu _
  exact sq_nonneg _

theorem FP_det_proxy :
    ∃ det : ℝ, 0 < det := ⟨1, one_pos⟩

theorem BRST_proxy :
    True := trivial

-- SECTION 7: STANDARD MODEL

def SM_gauge_group_rank : ℕ := 12

theorem SM_rank_pos :
    0 < SM_gauge_group_rank := by
  unfold SM_gauge_group_rank; norm_num

noncomputable def higgs_potential
    (phi mu2 lambda : ℝ)
    (hlambda : 0 < lambda) : ℝ :=
  -mu2 * phi ^ 2 + lambda * phi ^ 4

noncomputable def higgs_vev
    (mu2 lambda : ℝ)
    (hmu : 0 < mu2) (hlambda : 0 < lambda) : ℝ :=
  Real.sqrt (mu2 / (2 * lambda))

theorem higgs_vev_pos
    (mu2 lambda : ℝ)
    (hmu : 0 < mu2) (hlambda : 0 < lambda) :
    0 < higgs_vev mu2 lambda hmu hlambda := by
  unfold higgs_vev
  apply Real.sqrt_pos_of_pos
  positivity

noncomputable def W_mass
    (g v : ℝ) (hg : 0 < g) (hv : 0 < v) : ℝ :=
  g * v / 2

theorem W_mass_pos
    (g v : ℝ) (hg : 0 < g) (hv : 0 < v) :
    0 < W_mass g v hg hv := by
  unfold W_mass; positivity

-- SECTION 8: SUPERSYMMETRY

theorem SUSY_algebra_proxy
    (H : ℝ) (hH : 0 ≤ H) :
    0 ≤ 2 * H := by linarith

def superpartner_mass (m : ℝ) : ℝ := m

theorem superpartner_pos (m : ℝ) (hm : 0 < m) :
    0 < superpartner_mass m := hm

noncomputable def SUSY_breaking_scale
    (F : ℝ) (hF : 0 < F) : ℝ :=
  Real.sqrt F

theorem SUSY_scale_pos
    (F : ℝ) (hF : 0 < F) :
    0 < SUSY_breaking_scale F hF :=
  Real.sqrt_pos_of_pos hF

theorem R_symmetry_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

-- SECTION 9: AWM QFT BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_Z :=
  euclidean_partition 21 1
    (fun i => (i.val : ℝ))

theorem domain_Z_pos :
    0 < domain_Z :=
  euclidean_Z_pos 21 (by norm_num) 1
    (fun i => (i.val : ℝ))

noncomputable def domain_propagator :=
  propagator_proxy 1 0 (by norm_num)

theorem domain_prop_pos :
    0 < domain_propagator :=
  propagator_pos 1 0 (by norm_num)

noncomputable def domain_YM :=
  YM_action 21 (fun i j =>
    if i = j then 1 else 0)

theorem domain_YM_nonneg :
    0 ≤ domain_YM :=
  YM_action_nonneg 21 (fun i j =>
    if i = j then 1 else 0)

noncomputable def domain_ZPE :=
  zero_point_energy 1 21

theorem domain_ZPE_pos :
    0 < domain_ZPE :=
  ZPE_pos 1 21 (by norm_num) (by norm_num)

noncomputable def domain_vev :=
  higgs_vev 1 1 (by norm_num) (by norm_num)

theorem domain_vev_pos :
    0 < domain_vev :=
  higgs_vev_pos 1 1 (by norm_num) (by norm_num)

theorem domain_beta_neg :
    beta_function 1 1 < 0 :=
  asymptotic_freedom_proxy 1 (by norm_num)

noncomputable def domain_perturbation :=
  perturbation_series (1/10)
    (fun _ => 1) 21

theorem domain_perturbation_nonneg :
    0 ≤ domain_perturbation :=
  perturbation_nonneg (1/10) (by norm_num)
    (fun _ => 1) (fun _ => by norm_num) 21

-- SYSTEM LOCK

structure QuantumFieldTheoryLock where
  action_linear  : ∀ (n : ℕ)
                     (L1 L2 : Fin n → ℝ) (c : ℝ),
                     action n (fun i =>
                       L1 i + c * L2 i) =
                     action n L1 +
                     c * action n L2
  creation_pos   : ∀ n : ℕ,
                     0 < creation_norm n
  ZPE_pos        : ∀ (hbar omega : ℝ),
                     0 < hbar → 0 < omega →
                     0 < zero_point_energy
                       hbar omega
  Z_pos          : ∀ (n : ℕ), 0 < n →
                     ∀ (beta : ℝ)
                       (E : Fin n → ℝ),
                     0 < euclidean_partition
                       n beta E
  prop_pos       : ∀ (m t : ℝ) (hm : 0 < m),
                     0 < propagator_proxy m t hm
  perturb_nn     : ∀ (g : ℝ), 0 ≤ g →
                     ∀ (a : ℕ → ℝ),
                     (∀ n, 0 ≤ a n) →
                     ∀ N : ℕ,
                     0 ≤ perturbation_series g a N
  beta_neg       : ∀ (b0 : ℝ), 0 < b0 →
                     beta_function b0 1 < 0
  YM_nn          : ∀ (n : ℕ)
                     (F : Fin n → Fin n → ℝ),
                     0 ≤ YM_action n F
  higgs_vev_pos  : ∀ (mu2 lambda : ℝ)
                     (hmu : 0 < mu2) (hlambda : 0 < lambda),
                     0 < higgs_vev
                       mu2 lambda hmu hlambda
  W_mass_pos     : ∀ (g v : ℝ)
                     (hg : 0 < g) (hv : 0 < v),
                     0 < W_mass g v hg hv
  SUSY_nn        : ∀ H : ℝ, 0 ≤ H →
                     0 ≤ 2 * H
  dom_Z_pos      : 0 < domain_Z
  dom_prop_pos   : 0 < domain_propagator
  dom_YM_nn      : 0 ≤ domain_YM
  dom_ZPE_pos    : 0 < domain_ZPE
  dom_vev_pos    : 0 < domain_vev
  dom_beta_neg   : beta_function 1 1 < 0
  dom_perturb_nn : 0 ≤ domain_perturbation

def QFTLock : QuantumFieldTheoryLock where
  action_linear  := action_linear
  creation_pos   := creation_norm_pos
  ZPE_pos        := ZPE_pos
  Z_pos          := euclidean_Z_pos
  prop_pos       := propagator_pos
  perturb_nn     := perturbation_nonneg
  beta_neg       := asymptotic_freedom_proxy
  YM_nn          := YM_action_nonneg
  higgs_vev_pos  := higgs_vev_pos
  W_mass_pos     := W_mass_pos
  SUSY_nn        := SUSY_algebra_proxy
  dom_Z_pos      := domain_Z_pos
  dom_prop_pos   := domain_prop_pos
  dom_YM_nn      := domain_YM_nonneg
  dom_ZPE_pos    := domain_ZPE_pos
  dom_vev_pos    := domain_vev_pos
  dom_beta_neg   := domain_beta_neg
  dom_perturb_nn := domain_perturbation_nonneg

end QuantumFieldTheory
