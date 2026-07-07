import Mathlib

namespace NuclearPhysics

open Finset Real

-- ============================================================
-- SECTION 1: NUCLEAR STRUCTURE
-- ============================================================

noncomputable def binding_energy
    (Z N : ℕ) (m_p m_n M c : ℝ)
    (hc : 0 < c) : ℝ :=
  (Z * m_p + N * m_n - M) * c ^ 2

noncomputable def SEMF
    (Z N : ℕ)
    (a_v a_s a_c a_sym : ℝ) : ℝ :=
  let A := Z + N
  a_v * A - a_s * A ^ (2/3 : ℝ) -
  a_c * Z ^ 2 / A ^ (1/3 : ℝ) -
  a_sym * ((N : ℝ) - (Z : ℝ)) ^ 2 / A

noncomputable def nuclear_radius
    (R0 : ℝ) (A : ℕ) : ℝ :=
  R0 * (A : ℝ) ^ (1/3 : ℝ)

theorem nuclear_radius_nonneg
    (R0 : ℝ) (hR : 0 ≤ R0) (A : ℕ) :
    0 ≤ nuclear_radius R0 A := by
  unfold nuclear_radius
  apply mul_nonneg hR
  apply Real.rpow_nonneg
  exact Nat.cast_nonneg A

noncomputable def nuclear_density
    (m R : ℝ) (hR : 0 < R) : ℝ :=
  m / ((4/3) * Real.pi * R ^ 3)

theorem nuclear_density_pos
    (m R : ℝ) (hm : 0 < m) (hR : 0 < R) :
    0 < nuclear_density m R hR := by
  unfold nuclear_density
  apply div_pos hm
  apply mul_pos
  · apply mul_pos (by norm_num) Real.pi_pos
  · exact pow_pos hR 3

-- ============================================================
-- SECTION 2: RADIOACTIVE DECAY
-- ============================================================

noncomputable def decay_law
    (N0 lambda t : ℝ)
    (hl : 0 < lambda) : ℝ :=
  N0 * Real.exp (-lambda * t)

theorem decay_law_pos
    (N0 lambda t : ℝ)
    (hN : 0 < N0) (hl : 0 < lambda) :
    0 < decay_law N0 lambda t hl := by
  unfold decay_law
  exact mul_pos hN (Real.exp_pos _)

theorem decay_law_decreasing
    (N0 lambda : ℝ)
    (hN : 0 < N0) (hl : 0 < lambda)
    (s t : ℝ) (hst : s ≤ t) :
    decay_law N0 lambda t hl ≤
    decay_law N0 lambda s hl := by
  unfold decay_law
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hN)
  apply Real.exp_le_exp.mpr
  have key : lambda * s ≤ lambda * t :=
    mul_le_mul_of_nonneg_left hst (le_of_lt hl)
  linarith

noncomputable def half_life
    (lambda : ℝ) (hl : 0 < lambda) : ℝ :=
  Real.log 2 / lambda

theorem half_life_pos
    (lambda : ℝ) (hl : 0 < lambda) :
    0 < half_life lambda hl := by
  unfold half_life
  apply div_pos _ hl
  exact Real.log_pos (by norm_num)

noncomputable def activity
    (lambda N : ℝ) : ℝ :=
  lambda * N

theorem activity_nonneg
    (lambda N : ℝ)
    (hl : 0 ≤ lambda) (hN : 0 ≤ N) :
    0 ≤ activity lambda N :=
  mul_nonneg hl hN

-- ============================================================
-- SECTION 3: NUCLEAR REACTIONS
-- ============================================================

noncomputable def Q_value
    (m_i m_f c : ℝ) : ℝ :=
  (m_i - m_f) * c ^ 2

def is_exothermic (Q : ℝ) : Prop := 0 < Q

theorem Q_exothermic_proxy
    (m_i m_f c : ℝ)
    (h : m_f < m_i) (hc : 0 < c) :
    is_exothermic (Q_value m_i m_f c) := by
  unfold is_exothermic Q_value
  apply mul_pos _ (pow_pos hc 2)
  linarith

theorem cross_section_nonneg
    (sigma : ℝ) (h : 0 ≤ sigma) :
    0 ≤ sigma := h

noncomputable def coulomb_barrier
    (Z1 Z2 R e k : ℝ)
    (hR : 0 < R) (hk : 0 < k) : ℝ :=
  k * Z1 * Z2 * e ^ 2 / R

theorem coulomb_barrier_nonneg
    (Z1 Z2 R e k : ℝ)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2)
    (hR : 0 < R) (hk : 0 < k) (he : 0 ≤ e) :
    0 ≤ coulomb_barrier Z1 Z2 R e k hR hk := by
  unfold coulomb_barrier
  apply div_nonneg _ (le_of_lt hR)
  apply mul_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (le_of_lt hk) hZ1
    · exact hZ2
  · exact sq_nonneg e

-- ============================================================
-- SECTION 4: FISSION AND FUSION
-- ============================================================

noncomputable def fission_energy
    (mass_defect c : ℝ)
    (hm : 0 < mass_defect) (hc : 0 < c) : ℝ :=
  mass_defect * c ^ 2

theorem fission_energy_pos
    (mass_defect c : ℝ)
    (hm : 0 < mass_defect) (hc : 0 < c) :
    0 < fission_energy mass_defect c hm hc := by
  unfold fission_energy
  exact mul_pos hm (pow_pos hc 2)

def DT_fusion_energy_MeV : ℝ := 17.6

theorem DT_energy_pos :
    0 < DT_fusion_energy_MeV := by
  unfold DT_fusion_energy_MeV; norm_num

noncomputable def lawson_criterion
    (n tau T : ℝ) : ℝ :=
  n * tau * T

theorem lawson_nonneg
    (n tau T : ℝ)
    (hn : 0 ≤ n) (ht : 0 ≤ tau)
    (hT : 0 ≤ T) :
    0 ≤ lawson_criterion n tau T := by
  unfold lawson_criterion
  exact mul_nonneg (mul_nonneg hn ht) hT

noncomputable def critical_mass_proxy
    (rho sigma : ℝ)
    (hrho : 0 < rho) (hs : 0 < sigma) : ℝ :=
  1 / (rho * sigma)

theorem critical_mass_pos
    (rho sigma : ℝ)
    (hrho : 0 < rho) (hs : 0 < sigma) :
    0 < critical_mass_proxy rho sigma hrho hs := by
  unfold critical_mass_proxy
  positivity

-- ============================================================
-- SECTION 5: NUCLEAR MODELS
-- ============================================================

def is_magic_number (n : ℕ) : Prop :=
  n ∈ ({2, 8, 20, 28, 50, 82, 126} : Finset ℕ)

theorem two_is_magic : is_magic_number 2 := by
  unfold is_magic_number; decide

theorem eight_is_magic : is_magic_number 8 := by
  unfold is_magic_number; decide

noncomputable def liquid_drop_energy (A : ℕ) : ℝ :=
  15.8 * A - 18.3 * (A : ℝ) ^ (2/3 : ℝ)

noncomputable def deformation_param
    (Q_2 R0 Z : ℝ)
    (hZ : 0 < Z) (hR : 0 < R0) : ℝ :=
  Q_2 / (Z * R0 ^ 2)

-- ============================================================
-- SECTION 6: PARTICLE PHYSICS BASICS
-- ============================================================

noncomputable def mass_energy
    (m c : ℝ) (hm : 0 ≤ m) (hc : 0 < c) : ℝ :=
  m * c ^ 2

theorem mass_energy_nonneg
    (m c : ℝ) (hm : 0 ≤ m) (hc : 0 < c) :
    0 ≤ mass_energy m c hm hc := by
  unfold mass_energy
  exact mul_nonneg hm (pow_pos hc 2 |>.le)

noncomputable def de_broglie
    (h p : ℝ) (hp : 0 < p) : ℝ :=
  h / p

theorem de_broglie_pos
    (h p : ℝ) (hh : 0 < h) (hp : 0 < p) :
    0 < de_broglie h p hp :=
  div_pos hh hp

theorem uncertainty_proxy
    (dx dp hbar : ℝ)
    (hdx : 0 < dx) (hdp : 0 < dp)
    (hh : 0 < hbar)
    (h : dx * dp ≥ hbar / 2) :
    dx * dp ≥ hbar / 2 := h

-- ============================================================
-- SECTION 7: NUCLEAR DETECTORS
-- ============================================================

noncomputable def energy_resolution
    (delta_E E : ℝ) (hE : 0 < E) : ℝ :=
  delta_E / E

theorem resolution_nonneg
    (delta_E E : ℝ)
    (hd : 0 ≤ delta_E) (hE : 0 < E) :
    0 ≤ energy_resolution delta_E E hE :=
  div_nonneg hd (le_of_lt hE)

noncomputable def detection_efficiency
    (N_det N_total : ℕ)
    (hN : 0 < N_total) : ℝ :=
  N_det / N_total

theorem efficiency_nonneg
    (N_det N_total : ℕ)
    (hN : 0 < N_total) :
    0 ≤ detection_efficiency N_det N_total hN := by
  unfold detection_efficiency
  positivity

theorem bragg_peak_nonneg
    (dE_dx : ℝ) (h : 0 ≤ dE_dx) :
    0 ≤ dE_dx := h

-- ============================================================
-- SECTION 8: RADIATION PROTECTION
-- ============================================================

noncomputable def absorbed_dose
    (E m : ℝ) (hm : 0 < m) : ℝ :=
  E / m

theorem dose_nonneg
    (E m : ℝ) (hE : 0 ≤ E) (hm : 0 < m) :
    0 ≤ absorbed_dose E m hm :=
  div_nonneg hE (le_of_lt hm)

noncomputable def effective_dose
    (w_R D : ℝ) : ℝ :=
  w_R * D

theorem effective_dose_nonneg
    (w_R D : ℝ) (hw : 0 ≤ w_R) (hD : 0 ≤ D) :
    0 ≤ effective_dose w_R D :=
  mul_nonneg hw hD

theorem ALARA_proxy (dose : ℝ)
    (h : 0 ≤ dose) : 0 ≤ dose := h

noncomputable def shielding_attenuation
    (I0 mu x : ℝ)
    (hmu : 0 < mu) : ℝ :=
  I0 * Real.exp (-mu * x)

theorem shielding_pos
    (I0 mu x : ℝ)
    (hI : 0 < I0) (hmu : 0 < mu) :
    0 < shielding_attenuation I0 mu x hmu :=
  mul_pos hI (Real.exp_pos _)

-- ============================================================
-- SECTION 9: AWM NUCLEAR PHYSICS BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_nuclear_radius :=
  nuclear_radius 1.2 21

theorem domain_radius_nonneg :
    0 ≤ domain_nuclear_radius :=
  nuclear_radius_nonneg 1.2 (by norm_num) 21

noncomputable def domain_decay :=
  decay_law 21 1 0 (by norm_num)

theorem domain_decay_pos :
    0 < domain_decay :=
  decay_law_pos 21 1 0 (by norm_num) (by norm_num)

noncomputable def domain_half_life :=
  half_life 1 (by norm_num)

theorem domain_half_life_pos :
    0 < domain_half_life :=
  half_life_pos 1 (by norm_num)

noncomputable def domain_lawson :=
  lawson_criterion 1e20 1 1e8

theorem domain_lawson_nonneg :
    0 ≤ domain_lawson :=
  lawson_nonneg 1e20 1 1e8
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def domain_mass_energy :=
  mass_energy 21 (3e8) (by norm_num)
    (by norm_num)

theorem domain_mass_energy_nonneg :
    0 ≤ domain_mass_energy :=
  mass_energy_nonneg 21 (3e8)
    (by norm_num) (by norm_num)

noncomputable def domain_dose :=
  effective_dose 1 0.001

theorem domain_dose_nonneg :
    0 ≤ domain_dose :=
  effective_dose_nonneg 1 0.001
    (by norm_num) (by norm_num)

theorem domain_DT_pos :
    0 < DT_fusion_energy_MeV :=
  DT_energy_pos

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure NuclearPhysicsLock where
  radius_nn      : ∀ (R0 : ℝ),
                     0 ≤ R0 →
                     ∀ (A : ℕ),
                     0 ≤ nuclear_radius R0 A
  decay_pos      : ∀ (N0 lambda t : ℝ)
                     (hN : 0 < N0) (hl : 0 < lambda),
                     0 < decay_law N0 lambda t hl
  half_life_pos  : ∀ (lambda : ℝ) (hl : 0 < lambda),
                     0 < half_life lambda hl
  activity_nn    : ∀ (lambda N : ℝ),
                     0 ≤ lambda → 0 ≤ N →
                     0 ≤ activity lambda N
  Q_exo          : ∀ (m_i m_f c : ℝ),
                     m_f < m_i → 0 < c →
                     is_exothermic
                       (Q_value m_i m_f c)
  fission_pos    : ∀ (md c : ℝ)
                     (hm : 0 < md) (hc : 0 < c),
                     0 < fission_energy
                       md c hm hc
  DT_pos         : 0 < DT_fusion_energy_MeV
  lawson_nn      : ∀ (n tau T : ℝ),
                     0 ≤ n → 0 ≤ tau → 0 ≤ T →
                     0 ≤ lawson_criterion n tau T
  mass_E_nn      : ∀ (m c : ℝ)
                     (hm : 0 ≤ m) (hc : 0 < c),
                     0 ≤ mass_energy m c hm hc
  dose_nn        : ∀ (w_R D : ℝ),
                     0 ≤ w_R → 0 ≤ D →
                     0 ≤ effective_dose w_R D
  shield_pos     : ∀ (I0 mu x : ℝ)
                     (hI : 0 < I0) (hmu : 0 < mu),
                     0 < shielding_attenuation
                       I0 mu x hmu
  magic_2        : is_magic_number 2
  magic_8        : is_magic_number 8
  dom_radius_nn  : 0 ≤ domain_nuclear_radius
  dom_decay_pos  : 0 < domain_decay
  dom_hl_pos     : 0 < domain_half_life
  dom_lawson_nn  : 0 ≤ domain_lawson
  dom_mE_nn      : 0 ≤ domain_mass_energy
  dom_dose_nn    : 0 ≤ domain_dose

def NPLock : NuclearPhysicsLock where
  radius_nn      := nuclear_radius_nonneg
  decay_pos      := decay_law_pos
  half_life_pos  := half_life_pos
  activity_nn    := activity_nonneg
  Q_exo          := Q_exothermic_proxy
  fission_pos    := fission_energy_pos
  DT_pos         := DT_energy_pos
  lawson_nn      := lawson_nonneg
  mass_E_nn      := mass_energy_nonneg
  dose_nn        := effective_dose_nonneg
  shield_pos     := shielding_pos
  magic_2        := two_is_magic
  magic_8        := eight_is_magic
  dom_radius_nn  := domain_radius_nonneg
  dom_decay_pos  := domain_decay_pos
  dom_hl_pos     := domain_half_life_pos
  dom_lawson_nn  := domain_lawson_nonneg
  dom_mE_nn      := domain_mass_energy_nonneg
  dom_dose_nn    := domain_dose_nonneg

end NuclearPhysics
