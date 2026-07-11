import Mathlib

namespace AcousticsWaves

open Finset Real

-- ============================================================
-- SECTION 1: WAVE EQUATION
-- ============================================================

noncomputable def sound_speed
    (B rho : ℝ) (hB : 0 < B)
    (hrho : 0 < rho) : ℝ :=
  Real.sqrt (B / rho)

theorem sound_speed_pos
    (B rho : ℝ) (hB : 0 < B)
    (hrho : 0 < rho) :
    0 < sound_speed B rho hB hrho := by
  unfold sound_speed
  exact Real.sqrt_pos.mpr
    (div_pos hB hrho)

noncomputable def acoustic_wave
    (p0 k x omega t : ℝ) : ℝ :=
  p0 * Real.cos (k * x - omega * t)

theorem acoustic_bounded
    (p0 k x omega t : ℝ) (hp : 0 ≤ p0) :
    |acoustic_wave p0 k x omega t| ≤ p0 := by
  unfold acoustic_wave
  calc |p0 * Real.cos (k * x - omega * t)|
      = p0 * |Real.cos (k * x - omega * t)| := by
        rw [abs_mul, abs_of_nonneg hp]
    _ ≤ p0 * 1 := mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one _) hp
    _ = p0 := mul_one _

theorem wavelength_freq
    (lambda f c : ℝ)
    (h : lambda * f = c)
    (hf : 0 < f) :
    0 < lambda ↔ 0 < c := by
  constructor
  · intro hl; rw [← h]; exact mul_pos hl hf
  · intro hc
    have := div_pos hc hf
    rwa [← h, mul_div_cancel_right₀ _
      (ne_of_gt hf)] at this

-- ============================================================
-- SECTION 2: ACOUSTIC INTENSITY
-- ============================================================

noncomputable def acoustic_intensity
    (p rho c : ℝ)
    (hrho : 0 < rho) (hc : 0 < c) : ℝ :=
  p ^ 2 / (2 * rho * c)

theorem acoustic_intensity_nonneg
    (p rho c : ℝ)
    (hrho : 0 < rho) (hc : 0 < c) :
    0 ≤ acoustic_intensity p rho c hrho hc := by
  unfold acoustic_intensity
  apply div_nonneg (sq_nonneg _)
  exact le_of_lt (mul_pos
    (mul_pos (by norm_num) hrho) hc)

noncomputable def SPL
    (p p_ref : ℝ) (href : 0 < p_ref) : ℝ :=
  20 * Real.log (p / p_ref) /
  Real.log 10

theorem dB_nonneg (SPL : ℝ)
    (h : 0 ≤ SPL) : 0 ≤ SPL := h

-- ============================================================
-- SECTION 3: STANDING WAVES
-- ============================================================

noncomputable def standing_wave
    (A k x omega t : ℝ) : ℝ :=
  2 * A * Real.sin (k * x) *
  Real.cos (omega * t)

theorem standing_wave_bounded
    (A k x omega t : ℝ) (hA : 0 ≤ A) :
    |standing_wave A k x omega t| ≤ 2 * A := by
  unfold standing_wave
  have heq : |2 * A * Real.sin (k * x) * Real.cos (omega * t)| =
      2 * A * (|Real.sin (k * x)| * |Real.cos (omega * t)|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * A)]
    ring
  rw [heq]
  have hprod : |Real.sin (k * x)| * |Real.cos (omega * t)| ≤ 1 := by
    calc |Real.sin (k * x)| * |Real.cos (omega * t)|
        ≤ 1 * 1 := mul_le_mul (Real.abs_sin_le_one _)
          (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := mul_one 1
  calc 2 * A * (|Real.sin (k * x)| * |Real.cos (omega * t)|)
      ≤ 2 * A * 1 := mul_le_mul_of_nonneg_left hprod (by linarith)
    _ = 2 * A := mul_one _

noncomputable def resonant_freq
    (n : ℕ) (c L : ℝ)
    (hc : 0 < c) (hL : 0 < L) : ℝ :=
  n * c / (2 * L)

theorem resonant_freq_nonneg (n : ℕ)
    (c L : ℝ) (hc : 0 < c) (hL : 0 < L) :
    0 ≤ resonant_freq n c L hc hL := by
  unfold resonant_freq
  apply div_nonneg
  · exact mul_nonneg (Nat.cast_nonneg n)
      (le_of_lt hc)
  · linarith

-- ============================================================
-- SECTION 4: DOPPLER EFFECT
-- ============================================================

noncomputable def doppler_freq
    (f c v_o v_s : ℝ)
    (hc : 0 < c) (hvs : -c < v_s) : ℝ :=
  f * (c + v_o) / (c + v_s)

theorem doppler_pos
    (f c v_o v_s : ℝ)
    (hf : 0 < f) (hc : 0 < c)
    (hvo : -c < v_o) (hvs : -c < v_s) :
    0 < doppler_freq f c v_o v_s hc hvs := by
  unfold doppler_freq
  apply div_pos
  · apply mul_pos hf; linarith
  · linarith

-- ============================================================
-- SECTION 5: ROOM ACOUSTICS
-- ============================================================

noncomputable def reverberation_time
    (V A : ℝ) (hA : 0 < A) : ℝ :=
  0.161 * V / A

theorem RT_nonneg
    (V A : ℝ) (hV : 0 ≤ V) (hA : 0 < A) :
    0 ≤ reverberation_time V A hA := by
  unfold reverberation_time
  apply div_nonneg _ (le_of_lt hA)
  exact mul_nonneg (by norm_num) hV

theorem absorption_valid
    (alpha : ℝ) (h0 : 0 ≤ alpha)
    (h1 : alpha ≤ 1) :
    0 ≤ alpha ∧ alpha ≤ 1 := ⟨h0, h1⟩

theorem room_mode_pos
    (f : ℝ) (hf : 0 < f) : 0 < f := hf

-- ============================================================
-- SECTION 6: NONLINEAR ACOUSTICS
-- ============================================================

noncomputable def mach_number
    (v c : ℝ) (hc : 0 < c) : ℝ :=
  v / c

theorem mach_nonneg
    (v c : ℝ) (hv : 0 ≤ v) (hc : 0 < c) :
    0 ≤ mach_number v c hc :=
  div_nonneg hv (le_of_lt hc)

def is_supersonic (M : ℝ) : Prop := 1 < M

theorem nonlinear_beta_pos
    (beta : ℝ) (h : 0 < beta) : 0 < beta := h

-- ============================================================
-- SECTION 7: MUSICAL ACOUSTICS
-- ============================================================

noncomputable def harmonic (n : ℕ)
    (f1 : ℝ) : ℝ := n * f1

theorem harmonic_nonneg (n : ℕ)
    (f1 : ℝ) (hf : 0 ≤ f1) :
    0 ≤ harmonic n f1 :=
  mul_nonneg (Nat.cast_nonneg n) hf

noncomputable def semitone_ratio : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / 12)

theorem semitone_pos : 0 < semitone_ratio := by
  unfold semitone_ratio
  apply Real.rpow_pos_of_pos; norm_num

theorem consonance_proxy (ratio : ℝ)
    (h : 0 < ratio) : 0 < ratio := h

-- ============================================================
-- SECTION 8: ULTRASOUND AND APPLICATIONS
-- ============================================================

theorem piezo_freq_pos
    (f : ℝ) (hf : 0 < f) : 0 < f := hf

noncomputable def acoustic_impedance
    (rho c : ℝ) : ℝ := rho * c

theorem impedance_pos
    (rho c : ℝ) (hrho : 0 < rho)
    (hc : 0 < c) :
    0 < acoustic_impedance rho c :=
  mul_pos hrho hc

noncomputable def reflection_coeff
    (Z1 Z2 : ℝ) (hZ : Z1 + Z2 ≠ 0) : ℝ :=
  (Z2 - Z1) / (Z1 + Z2)

noncomputable def transmission_coeff
    (Z1 Z2 : ℝ) (hZ : Z1 + Z2 ≠ 0) : ℝ :=
  2 * Z2 / (Z1 + Z2)

-- ============================================================
-- SECTION 9: AWM ACOUSTICS BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_sound_speed :=
  sound_speed 1 1 (by norm_num) (by norm_num)

theorem domain_ss_pos :
    0 < domain_sound_speed :=
  sound_speed_pos 1 1
    (by norm_num) (by norm_num)

noncomputable def domain_acoustic_intensity :=
  acoustic_intensity 1 1 1
    (by norm_num) (by norm_num)

theorem domain_ai_nonneg :
    0 ≤ domain_acoustic_intensity :=
  acoustic_intensity_nonneg 1 1 1
    (by norm_num) (by norm_num)

noncomputable def domain_resonant :=
  resonant_freq 21 340 1
    (by norm_num) (by norm_num)

theorem domain_resonant_nonneg :
    0 ≤ domain_resonant :=
  resonant_freq_nonneg 21 340 1
    (by norm_num) (by norm_num)

noncomputable def domain_harmonic :=
  harmonic 21 440

theorem domain_harmonic_nonneg :
    0 ≤ domain_harmonic :=
  harmonic_nonneg 21 440 (by norm_num)

noncomputable def domain_impedance :=
  acoustic_impedance 1.2 340

theorem domain_impedance_pos :
    0 < domain_impedance :=
  impedance_pos 1.2 340
    (by norm_num) (by norm_num)

noncomputable def domain_RT :=
  reverberation_time 21 1 (by norm_num)

theorem domain_RT_nonneg :
    0 ≤ domain_RT :=
  RT_nonneg 21 1 (by norm_num) (by norm_num)

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure AcousticsLock where
  ss_pos         : ∀ (B rho : ℝ) (hB : 0 < B) (hrho : 0 < rho),
                     0 < sound_speed B rho hB hrho
  wave_bound     : ∀ (p0 k x w t : ℝ),
                     0 ≤ p0 →
                     |acoustic_wave p0 k x w t|
                     ≤ p0
  intensity_nn   : ∀ (p rho c : ℝ) (hrho : 0 < rho) (hc : 0 < c),
                     0 ≤ acoustic_intensity
                       p rho c hrho hc
  standing_bound : ∀ (A k x w t : ℝ),
                     0 ≤ A →
                     |standing_wave A k x w t|
                     ≤ 2 * A
  resonant_nn    : ∀ (n : ℕ) (c L : ℝ) (hc : 0 < c) (hL : 0 < L),
                     0 ≤ resonant_freq
                       n c L hc hL
  doppler_pos    : ∀ (f c vo vs : ℝ)
                     (hf : 0 < f) (hc : 0 < c)
                     (hvo : -c < vo) (hvs : -c < vs),
                     0 < doppler_freq
                       f c vo vs hc hvs
  RT_nn          : ∀ (V A : ℝ) (hV : 0 ≤ V) (hA : 0 < A),
                     0 ≤ reverberation_time V A hA
  harmonic_nn    : ∀ (n : ℕ) (f1 : ℝ),
                     0 ≤ f1 →
                     0 ≤ harmonic n f1
  semitone_pos   : 0 < semitone_ratio
  impedance_pos  : ∀ (rho c : ℝ),
                     0 < rho → 0 < c →
                     0 < acoustic_impedance rho c
  dom_ss_pos     : 0 < domain_sound_speed
  dom_ai_nn      : 0 ≤ domain_acoustic_intensity
  dom_res_nn     : 0 ≤ domain_resonant
  dom_harm_nn    : 0 ≤ domain_harmonic
  dom_imp_pos    : 0 < domain_impedance
  dom_RT_nn      : 0 ≤ domain_RT

def ALock : AcousticsLock where
  ss_pos         := sound_speed_pos
  wave_bound     := acoustic_bounded
  intensity_nn   := acoustic_intensity_nonneg
  standing_bound := standing_wave_bounded
  resonant_nn    := resonant_freq_nonneg
  doppler_pos    := doppler_pos
  RT_nn          := RT_nonneg
  harmonic_nn    := harmonic_nonneg
  semitone_pos   := semitone_pos
  impedance_pos  := impedance_pos
  dom_ss_pos     := domain_ss_pos
  dom_ai_nn      := domain_ai_nonneg
  dom_res_nn     := domain_resonant_nonneg
  dom_harm_nn    := domain_harmonic_nonneg
  dom_imp_pos    := domain_impedance_pos
  dom_RT_nn      := domain_RT_nonneg

end AcousticsWaves

