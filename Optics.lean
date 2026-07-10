import Mathlib

namespace Optics

open Finset Real

-- ============================================================
-- SECTION 1: GEOMETRIC OPTICS
-- ============================================================

def snells_law (n1 n2 theta1 theta2 : ℝ) : Prop :=
  n1 * Real.sin theta1 = n2 * Real.sin theta2

noncomputable def critical_angle
    (n1 n2 : ℝ) (hn1 : 0 < n1) : ℝ :=
  Real.arcsin (n2 / n1)

def thin_lens (f d_o d_i : ℝ) : Prop :=
  1 / f = 1 / d_o + 1 / d_i

noncomputable def magnification
    (d_i d_o : ℝ) (hdo : 0 < d_o) : ℝ :=
  -d_i / d_o

theorem refractive_index_pos
    (n : ℝ) (hn : 1 ≤ n) : 0 < n := by
  linarith

-- ============================================================
-- SECTION 2: WAVE OPTICS
-- ============================================================

noncomputable def optical_wave
    (E0 k x omega t : ℝ) : ℝ :=
  E0 * Real.cos (k * x - omega * t)

theorem wave_bounded
    (E0 k x omega t : ℝ) (hE : 0 ≤ E0) :
    |optical_wave E0 k x omega t| ≤ E0 := by
  unfold optical_wave
  calc |E0 * Real.cos (k * x - omega * t)|
      = E0 * |Real.cos (k * x - omega * t)| := by
        rw [abs_mul, abs_of_nonneg hE]
    _ ≤ E0 * 1 := by
        apply mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one _) hE
    _ = E0 := mul_one _

noncomputable def intensity
    (E0 eps0 c : ℝ) : ℝ :=
  eps0 * c * E0 ^ 2 / 2

theorem intensity_nonneg
    (E0 eps0 c : ℝ)
    (heps : 0 ≤ eps0) (hc : 0 ≤ c) :
    0 ≤ intensity E0 eps0 c := by
  unfold intensity
  apply div_nonneg _ (by norm_num)
  exact mul_nonneg (mul_nonneg heps hc)
    (sq_nonneg E0)

-- ============================================================
-- SECTION 3: INTERFERENCE
-- ============================================================

noncomputable def path_difference
    (d theta : ℝ) : ℝ :=
  d * Real.sin theta

def constructive (delta lambda : ℝ)
    (m : ℤ) : Prop :=
  delta = m * lambda

def destructive (delta lambda : ℝ)
    (m : ℤ) : Prop :=
  delta = (2 * m + 1) * lambda / 2

noncomputable def fringe_spacing
    (lambda L d : ℝ)
    (hd : 0 < d) : ℝ :=
  lambda * L / d

theorem fringe_spacing_pos
    (lambda L d : ℝ)
    (hlam : 0 < lambda) (hL : 0 < L)
    (hd : 0 < d) :
    0 < fringe_spacing lambda L d hd := by
  unfold fringe_spacing
  exact div_pos (mul_pos hlam hL) hd

-- ============================================================
-- SECTION 4: DIFFRACTION
-- ============================================================

noncomputable def single_slit_intensity
    (I0 beta : ℝ) (hI : 0 ≤ I0) : ℝ :=
  if beta = 0 then I0
  else I0 * (Real.sin (beta / 2) /
    (beta / 2)) ^ 2

theorem single_slit_nonneg
    (I0 beta : ℝ) (hI : 0 ≤ I0) :
    0 ≤ single_slit_intensity I0 beta hI := by
  unfold single_slit_intensity
  split_ifs with h
  · exact hI
  · apply mul_nonneg hI (sq_nonneg _)

noncomputable def rayleigh_criterion
    (lambda D : ℝ) (hD : 0 < D) : ℝ :=
  1.22 * lambda / D

theorem rayleigh_pos
    (lambda D : ℝ)
    (hlam : 0 < lambda) (hD : 0 < D) :
    0 < rayleigh_criterion lambda D hD := by
  unfold rayleigh_criterion
  exact div_pos (by linarith) hD

-- ============================================================
-- SECTION 5: POLARIZATION
-- ============================================================

noncomputable def malus_law
    (I0 theta : ℝ) : ℝ :=
  I0 * Real.cos theta ^ 2

theorem malus_nonneg
    (I0 theta : ℝ) (hI : 0 ≤ I0) :
    0 ≤ malus_law I0 theta := by
  unfold malus_law
  exact mul_nonneg hI (sq_nonneg _)

theorem malus_le_I0
    (I0 theta : ℝ) (hI : 0 ≤ I0) :
    malus_law I0 theta ≤ I0 := by
  unfold malus_law
  have h1 : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have h2 : -1 ≤ Real.cos theta := Real.neg_one_le_cos theta
  have hsq : Real.cos theta ^ 2 ≤ 1 := by nlinarith
  calc I0 * Real.cos theta ^ 2 ≤ I0 * 1 :=
        mul_le_mul_of_nonneg_left hsq hI
    _ = I0 := mul_one _

noncomputable def brewster_angle
    (n1 n2 : ℝ) (hn1 : 0 < n1) : ℝ :=
  Real.arctan (n2 / n1)

-- ============================================================
-- SECTION 6: LASERS
-- ============================================================

theorem einstein_A_nonneg
    (A : ℝ) (hA : 0 ≤ A) : 0 ≤ A := hA

def population_inversion
    (N2 N1 : ℝ) : Prop := N1 < N2

theorem laser_threshold_proxy
    (g_th : ℝ) (h : 0 < g_th) : 0 < g_th := h

noncomputable def coherence_length
    (lambda delta_lambda : ℝ)
    (hd : 0 < delta_lambda) : ℝ :=
  lambda ^ 2 / delta_lambda

theorem coherence_nonneg
    (lambda delta_lambda : ℝ)
    (hd : 0 < delta_lambda) :
    0 ≤ coherence_length lambda delta_lambda hd := by
  unfold coherence_length
  exact div_nonneg (sq_nonneg _)
    (le_of_lt hd)

-- ============================================================
-- SECTION 7: FIBER OPTICS
-- ============================================================

noncomputable def numerical_aperture
    (n1 n2 : ℝ) (h : n2 < n1) : ℝ :=
  Real.sqrt (n1 ^ 2 - n2 ^ 2)

theorem NA_nonneg
    (n1 n2 : ℝ) (h : n2 < n1) :
    0 ≤ numerical_aperture n1 n2 h := by
  unfold numerical_aperture
  apply Real.sqrt_nonneg

theorem acceptance_angle_nonneg
    (theta : ℝ) (h : 0 ≤ theta) :
    0 ≤ theta := h

noncomputable def fiber_attenuation
    (alpha L : ℝ) (hL : 0 ≤ L) : ℝ :=
  Real.exp (-alpha * L)

theorem attenuation_pos
    (alpha L : ℝ) (hL : 0 ≤ L) :
    0 < fiber_attenuation alpha L hL :=
  Real.exp_pos _

-- ============================================================
-- SECTION 8: QUANTUM OPTICS
-- ============================================================

noncomputable def photon_energy
    (h nu : ℝ) (hh : 0 < h)
    (hnu : 0 < nu) : ℝ :=
  h * nu

theorem photon_energy_pos
    (h nu : ℝ) (hh : 0 < h)
    (hnu : 0 < nu) :
    0 < photon_energy h nu hh hnu :=
  mul_pos hh hnu

noncomputable def photon_momentum
    (h lambda : ℝ) (hlam : 0 < lambda) : ℝ :=
  h / lambda

theorem photon_momentum_pos
    (h lambda : ℝ) (hh : 0 < h)
    (hlam : 0 < lambda) :
    0 < photon_momentum h lambda hlam :=
  div_pos hh hlam

theorem squeezed_light_proxy :
    True := trivial

-- ============================================================
-- SECTION 9: AWM OPTICS BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_intensity :=
  intensity 1 1 1

theorem domain_intensity_nonneg :
    0 ≤ domain_intensity :=
  intensity_nonneg 1 1 1
    (by norm_num) (by norm_num)

noncomputable def domain_fringe :=
  fringe_spacing 500e-9 1 0.001
    (by norm_num)

theorem domain_fringe_pos :
    0 < domain_fringe :=
  fringe_spacing_pos 500e-9 1 0.001
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def domain_malus :=
  malus_law 1 (Real.pi / 4)

theorem domain_malus_nonneg :
    0 ≤ domain_malus :=
  malus_nonneg 1 (Real.pi / 4) (by norm_num)

noncomputable def domain_photon :=
  photon_energy 6.626e-34 5e14
    (by norm_num) (by norm_num)

theorem domain_photon_pos :
    0 < domain_photon :=
  photon_energy_pos 6.626e-34 5e14
    (by norm_num) (by norm_num)

noncomputable def domain_coherence :=
  coherence_length 500e-9 1e-9
    (by norm_num)

theorem domain_coherence_nonneg :
    0 ≤ domain_coherence :=
  coherence_nonneg 500e-9 1e-9
    (by norm_num)

theorem NA_input_lt : (1.0:ℝ) < 1.5 := by norm_num

noncomputable def domain_NA :=
  numerical_aperture 1.5 1.0 NA_input_lt

theorem domain_NA_nonneg :
    0 ≤ domain_NA :=
  NA_nonneg 1.5 1.0 NA_input_lt

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure OpticsLock where
  ref_idx_pos    : ∀ n : ℝ, 1 ≤ n → 0 < n
  wave_bounded   : ∀ (E0 k x w t : ℝ),
                     0 ≤ E0 →
                     |optical_wave E0 k x w t|
                     ≤ E0
  intensity_nn   : ∀ (E0 e0 c : ℝ),
                     0 ≤ e0 → 0 ≤ c →
                     0 ≤ intensity E0 e0 c
  fringe_pos     : ∀ (lam L d : ℝ)
                     (hlam : 0 < lam)
                     (hL : 0 < L) (hd : 0 < d),
                     0 < fringe_spacing lam L d hd
  slit_nn        : ∀ (I0 beta : ℝ)
                     (hI : 0 ≤ I0),
                     0 ≤ single_slit_intensity
                       I0 beta hI
  rayleigh_pos   : ∀ (lam D : ℝ)
                     (hlam : 0 < lam) (hD : 0 < D),
                     0 < rayleigh_criterion
                       lam D hD
  malus_nn       : ∀ (I0 theta : ℝ), 0 ≤ I0 →
                     0 ≤ malus_law I0 theta
  malus_le       : ∀ (I0 theta : ℝ), 0 ≤ I0 →
                     malus_law I0 theta ≤ I0
  coh_nn         : ∀ (lam dl : ℝ)
                     (hd : 0 < dl),
                     0 ≤ coherence_length lam dl hd
  photon_pos     : ∀ (h nu : ℝ)
                     (hh : 0 < h) (hnu : 0 < nu),
                     0 < photon_energy h nu hh hnu
  atten_pos      : ∀ (alpha L : ℝ)
                     (hL : 0 ≤ L),
                     0 < fiber_attenuation
                       alpha L hL
  dom_int_nn     : 0 ≤ domain_intensity
  dom_fringe_pos : 0 < domain_fringe
  dom_malus_nn   : 0 ≤ domain_malus
  dom_photon_pos : 0 < domain_photon
  dom_coh_nn     : 0 ≤ domain_coherence
  dom_NA_nn      : 0 ≤ domain_NA

def OLock : OpticsLock where
  ref_idx_pos    := refractive_index_pos
  wave_bounded   := wave_bounded
  intensity_nn   := intensity_nonneg
  fringe_pos     := fringe_spacing_pos
  slit_nn        := single_slit_nonneg
  rayleigh_pos   := rayleigh_pos
  malus_nn       := malus_nonneg
  malus_le       := malus_le_I0
  coh_nn         := coherence_nonneg
  photon_pos     := photon_energy_pos
  atten_pos      := attenuation_pos
  dom_int_nn     := domain_intensity_nonneg
  dom_fringe_pos := domain_fringe_pos
  dom_malus_nn   := domain_malus_nonneg
  dom_photon_pos := domain_photon_pos
  dom_coh_nn     := domain_coherence_nonneg
  dom_NA_nn      := domain_NA_nonneg

end Optics

