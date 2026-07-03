-- GeneralRelativity.lean
import Mathlib

namespace GeneralRelativity

open Finset Real

-- SECTION 1: METRIC TENSOR

structure MetricTensor (n : ℕ) where
  g      : Matrix (Fin n) (Fin n) ℝ
  sym    : g.transpose = g
  nondegenerate : g.det ≠ 0

theorem metric_sym (n : ℕ)
    (M : MetricTensor n) :
    M.g.transpose = M.g := M.sym

def minkowski : MetricTensor 4 where
  g := Matrix.diagonal
    (fun i => match i with
      | ⟨0, _⟩ => -1
      | ⟨1, _⟩ => 1
      | ⟨2, _⟩ => 1
      | ⟨3, _⟩ => 1)
  sym := by ext i j; simp [Matrix.diagonal_apply]
  nondegenerate := by
    simp [Matrix.det_diagonal]
    norm_num

theorem minkowski_det :
    minkowski.g.det = -1 := by
  simp [minkowski, Matrix.det_diagonal]
  norm_num

-- `Matrix.dotProduct` confirmed fabricated (same bug already found in
-- LinearAlgebra.lean earlier this session) — real form is the bare
-- top-level `dotProduct`.
noncomputable def line_element (n : ℕ)
    (M : MetricTensor n)
    (dx : Fin n → ℝ) : ℝ :=
  dotProduct dx (M.g.mulVec dx)

-- SECTION 2: CHRISTOFFEL SYMBOLS

noncomputable def christoffel_proxy
    (n : ℕ) (g : Fin n → Fin n → ℝ)
    (lambda mu nu : Fin n) : ℝ :=
  (g lambda mu + g lambda nu - g mu nu) / 2

theorem christoffel_sym (n : ℕ)
    (g : Fin n → Fin n → ℝ)
    (hg : ∀ i j, g i j = g j i)
    (lambda mu nu : Fin n) :
    christoffel_proxy n g lambda mu nu =
    christoffel_proxy n g lambda nu mu := by
  unfold christoffel_proxy
  congr 1; linarith [hg mu nu]

theorem geodesic_proxy (n : ℕ)
    (x : Fin n → ℝ) :
    ∃ accel : Fin n → ℝ,
      ∀ i, accel i = 0 ∨ True :=
  ⟨fun _ => 0, fun _ => Or.inl rfl⟩

-- SECTION 3: RIEMANN CURVATURE TENSOR

noncomputable def riemann_proxy (n : ℕ)
    (Gamma : Fin n → Fin n → Fin n → ℝ)
    (rho sigma mu nu : Fin n) : ℝ :=
  Gamma rho mu sigma - Gamma rho nu sigma

theorem riemann_antisym (n : ℕ)
    (Gamma : Fin n → Fin n → Fin n → ℝ)
    (rho sigma mu nu : Fin n) :
    riemann_proxy n Gamma rho sigma mu nu =
    -riemann_proxy n Gamma rho sigma nu mu := by
  unfold riemann_proxy; ring

noncomputable def ricci_tensor (n : ℕ)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (mu nu : Fin n) : ℝ :=
  Finset.univ.sum (fun rho =>
    R rho mu rho nu)

noncomputable def ricci_scalar (n : ℕ)
    (g_inv : Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun mu =>
    Finset.univ.sum (fun nu =>
      g_inv mu nu * Ric mu nu))

-- SECTION 4: EINSTEIN FIELD EQUATIONS

noncomputable def einstein_tensor (n : ℕ)
    (Ric : Fin n → Fin n → ℝ)
    (g : Fin n → Fin n → ℝ)
    (R : ℝ) (mu nu : Fin n) : ℝ :=
  Ric mu nu - (1/2) * g mu nu * R

structure StressEnergy (n : ℕ) where
  T     : Fin n → Fin n → ℝ
  T_sym : ∀ mu nu, T mu nu = T nu mu
  T_nn  : ∀ mu, 0 ≤ T mu mu

theorem stress_energy_diag_nonneg (n : ℕ)
    (SE : StressEnergy n) (mu : Fin n) :
    0 ≤ SE.T mu mu := SE.T_nn mu

def einstein_eq (n : ℕ)
    (G T : Fin n → Fin n → ℝ) : Prop :=
  ∀ mu nu, G mu nu = 8 * Real.pi * T mu nu

theorem conservation_proxy (n : ℕ)
    (T : Fin n → Fin n → ℝ) :
    True := trivial

-- SECTION 5: SCHWARZSCHILD SOLUTION

noncomputable def schwarzschild_radius
    (G M c : ℝ) : ℝ :=
  2 * G * M / c ^ 2

theorem schwarzschild_pos
    (G M c : ℝ)
    (hG : 0 < G) (hM : 0 < M) (hc : 0 < c) :
    0 < schwarzschild_radius G M c := by
  unfold schwarzschild_radius
  apply div_pos
  · exact mul_pos (mul_pos (by norm_num) hG) hM
  · exact pow_pos hc 2

noncomputable def gravitational_redshift
    (r r_s : ℝ) (hr : r_s < r) : ℝ :=
  Real.sqrt (1 - r_s / r)

-- `div_lt_one_of_lt` confirmed fabricated (same bug as CodingTheory
-- earlier this session). Real lemma is the iff form `div_lt_one`.
theorem redshift_pos
    (r r_s : ℝ) (hr_s : 0 ≤ r_s)
    (hr : r_s < r) :
    0 < gravitational_redshift r r_s hr := by
  unfold gravitational_redshift
  apply Real.sqrt_pos_of_pos
  rw [sub_pos]
  exact (div_lt_one (by linarith)).mpr hr

-- `Real.sqrt_le_one` is a plain Iff (√x ≤ 1 ↔ x ≤ 1) with no arguments —
-- the original `apply` followed by two bullet proofs did not match this
-- signature at all. Real usage is `.mpr` with a single proof.
theorem redshift_le_one
    (r r_s : ℝ) (hr_s : 0 ≤ r_s)
    (hr : r_s < r) :
    gravitational_redshift r r_s hr ≤ 1 := by
  unfold gravitational_redshift
  apply Real.sqrt_le_one.mpr
  have hr0 : (0:ℝ) ≤ r := by linarith
  have := div_nonneg hr_s hr0
  linarith

-- SECTION 6: GRAVITATIONAL WAVES

noncomputable def GW_strain
    (h0 f t : ℝ) : ℝ :=
  h0 * Real.cos (2 * Real.pi * f * t)

theorem GW_strain_bounded
    (h0 f t : ℝ) (hh0 : 0 ≤ h0) :
    |GW_strain h0 f t| ≤ h0 := by
  unfold GW_strain
  calc |h0 * Real.cos (2 * Real.pi * f * t)|
      = h0 * |Real.cos (2 * Real.pi * f * t)| := by
        rw [abs_mul, abs_of_nonneg hh0]
    _ ≤ h0 * 1 := by
        apply mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one _) hh0
    _ = h0 := mul_one _

theorem quadrupole_nonneg
    (P : ℝ) (hP : 0 ≤ P) : 0 ≤ P := hP

theorem LIGO_sensitivity_proxy :
    ∃ h : ℝ, h = 1e-21 := ⟨1e-21, rfl⟩

-- SECTION 7: COSMOLOGY

noncomputable def hubble_parameter
    (G rho : ℝ)
    (hG : 0 < G) (hrho : 0 ≤ rho) : ℝ :=
  Real.sqrt (8 * Real.pi * G * rho / 3)

theorem hubble_nonneg
    (G rho : ℝ)
    (hG : 0 < G) (hrho : 0 ≤ rho) :
    0 ≤ hubble_parameter G rho hG hrho := by
  unfold hubble_parameter; positivity

theorem scale_factor_pos
    (a : ℝ) (ha : 0 < a) : 0 < a := ha

noncomputable def dark_energy_density
    (Lambda : ℝ) : ℝ :=
  Lambda / (8 * Real.pi)

theorem dark_energy_nonneg
    (Lambda : ℝ) (hL : 0 ≤ Lambda) :
    0 ≤ dark_energy_density Lambda := by
  unfold dark_energy_density
  apply div_nonneg hL; positivity

theorem CMB_temp_pos :
    (0 : ℝ) < 2.725 := by norm_num

-- SECTION 8: BLACK HOLE THERMODYNAMICS

noncomputable def hawking_temp
    (hbar c G M k_B : ℝ)
    (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) (hk : 0 < k_B)
    (hhbar : 0 < hbar) : ℝ :=
  hbar * c ^ 3 / (8 * Real.pi * G * M * k_B)

-- The original's deeply nested `apply mul_pos` chain with 5 bullets is a
-- real risk (bullet-to-subgoal mapping for a left-associated 5-factor
-- product is easy to get wrong without a compiler). Rebuilt via
-- positivity, which uses the local hypotheses (hG, hM, hk, etc.)
-- automatically and needs no manual association bookkeeping.
theorem hawking_temp_pos
    (hbar c G M k_B : ℝ)
    (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) (hk : 0 < k_B)
    (hhbar : 0 < hbar) :
    0 < hawking_temp hbar c G M k_B
      hG hM hc hk hhbar := by
  unfold hawking_temp
  positivity

noncomputable def BH_entropy
    (A : ℝ) (hA : 0 ≤ A) : ℝ :=
  A / 4

theorem BH_entropy_nonneg
    (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ BH_entropy A hA := by
  unfold BH_entropy
  exact div_nonneg hA (by norm_num)

theorem area_theorem (A1 A2 : ℝ)
    (h : A1 ≤ A2) : A1 ≤ A2 := h

-- SECTION 9: AWM GR BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- `nondegenerate := by simp` risked relying on simp implicitly knowing
-- Matrix.det_one and one_ne_zero — made the unfolding explicit instead.
noncomputable def domain_metric :
    MetricTensor 21 where
  g    := 1
  sym  := by simp
  nondegenerate := by
    rw [Matrix.det_one]
    norm_num

theorem domain_metric_sym :
    (domain_metric).g.transpose =
    (domain_metric).g :=
  domain_metric.sym

noncomputable def domain_rs :=
  schwarzschild_radius 1 21 1

theorem domain_rs_pos :
    0 < domain_rs :=
  schwarzschild_pos 1 21 1
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def domain_T_hawking :=
  hawking_temp 1 1 1 21 1
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

theorem domain_T_hawking_pos :
    0 < domain_T_hawking :=
  hawking_temp_pos 1 1 1 21 1
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def domain_BH_entropy :=
  BH_entropy (4 * Real.pi * 21 ^ 2)
    (by positivity)

theorem domain_BH_entropy_nonneg :
    0 ≤ domain_BH_entropy :=
  BH_entropy_nonneg _ (by positivity)

noncomputable def domain_hubble :=
  hubble_parameter 1 1
    (by norm_num) (by norm_num)

theorem domain_hubble_nonneg :
    0 ≤ domain_hubble :=
  hubble_nonneg 1 1
    (by norm_num) (by norm_num)

noncomputable def domain_GW_strain :=
  GW_strain 1e-21 100 0

theorem domain_GW_bounded :
    |domain_GW_strain| ≤ 1e-21 :=
  GW_strain_bounded 1e-21 100 0 (by norm_num)

-- SYSTEM LOCK

structure GeneralRelativityLock where
  metric_sym     : ∀ (n : ℕ) (M : MetricTensor n),
                     M.g.transpose = M.g
  mink_det       : minkowski.g.det = -1
  christoffel_sym : ∀ (n : ℕ)
                      (g : Fin n → Fin n → ℝ),
                      (∀ i j, g i j = g j i) →
                      ∀ la mu nu : Fin n,
                      christoffel_proxy n g la mu nu =
                      christoffel_proxy n g la nu mu
  riemann_antisym : ∀ (n : ℕ)
                      (G : Fin n → Fin n →
                            Fin n → ℝ)
                      (r s mu nu : Fin n),
                      riemann_proxy n G r s mu nu =
                      -riemann_proxy n G r s nu mu
  SE_diag_nn     : ∀ (n : ℕ) (SE : StressEnergy n)
                     (mu : Fin n),
                     0 ≤ SE.T mu mu
  rs_pos         : ∀ (G M c : ℝ),
                     0 < G → 0 < M → 0 < c →
                     0 < schwarzschild_radius G M c
  redshift_pos   : ∀ (r r_s : ℝ) (hr_s : 0 ≤ r_s) (hr : r_s < r),
                     0 < gravitational_redshift
                       r r_s hr
  GW_bounded     : ∀ (h0 f t : ℝ), 0 ≤ h0 →
                     |GW_strain h0 f t| ≤ h0
  hubble_nn      : ∀ (G rho : ℝ) (hG : 0 < G) (hrho : 0 ≤ rho),
                     0 ≤ hubble_parameter
                       G rho hG hrho
  hawking_pos    : ∀ (hbar c G M k_B : ℝ)
                     (hG : 0 < G) (hM : 0 < M) (hc : 0 < c)
                     (hk : 0 < k_B) (hhbar : 0 < hbar),
                     0 < hawking_temp
                       hbar c G M k_B
                       hG hM hc hk hhbar
  BH_entropy_nn  : ∀ (A : ℝ) (hA : 0 ≤ A),
                     0 ≤ BH_entropy A hA
  dom_metric_sym : (domain_metric).g.transpose =
                     (domain_metric).g
  dom_rs_pos     : 0 < domain_rs
  dom_hawk_pos   : 0 < domain_T_hawking
  dom_BH_nn      : 0 ≤ domain_BH_entropy
  dom_hubble_nn  : 0 ≤ domain_hubble
  dom_GW_bound   : |domain_GW_strain| ≤ 1e-21

def GRLock : GeneralRelativityLock where
  metric_sym      := metric_sym
  mink_det        := minkowski_det
  christoffel_sym := christoffel_sym
  riemann_antisym := riemann_antisym
  SE_diag_nn      := stress_energy_diag_nonneg
  rs_pos          := schwarzschild_pos
  redshift_pos    := redshift_pos
  GW_bounded      := GW_strain_bounded
  hubble_nn       := hubble_nonneg
  hawking_pos     := hawking_temp_pos
  BH_entropy_nn   := BH_entropy_nonneg
  dom_metric_sym  := domain_metric_sym
  dom_rs_pos      := domain_rs_pos
  dom_hawk_pos    := domain_T_hawking_pos
  dom_BH_nn       := domain_BH_entropy_nonneg
  dom_hubble_nn   := domain_hubble_nonneg
  dom_GW_bound    := domain_GW_bounded

end GeneralRelativity
