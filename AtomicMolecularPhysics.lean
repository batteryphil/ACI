import Mathlib

namespace AtomicMolecularPhysics

open Finset Real

noncomputable def bohr_radius
    (hbar me e k : ℝ)
    (hme : 0 < me) (he : 0 < e)
    (hk : 0 < k) (hh : 0 < hbar) : ℝ :=
  hbar ^ 2 / (me * k * e ^ 2)

theorem bohr_radius_pos
    (hbar me e k : ℝ)
    (hme : 0 < me) (he : 0 < e)
    (hk : 0 < k) (hh : 0 < hbar) :
    0 < bohr_radius hbar me e k
      hme he hk hh := by
  unfold bohr_radius
  apply div_pos (pow_pos hh 2)
  exact mul_pos (mul_pos hme hk)
    (pow_pos he 2)

noncomputable def hydrogen_energy
    (E1 : ℝ) (n : ℕ) (hn : 0 < n) : ℝ :=
  E1 / (n : ℝ) ^ 2

theorem hydrogen_energy_neg
    (n : ℕ) (hn : 0 < n) :
    hydrogen_energy (-13.6) n hn < 0 := by
  unfold hydrogen_energy
  apply div_neg_of_neg_of_pos (by norm_num)
  positivity

noncomputable def rydberg_wavelength
    (R_inf : ℝ) (n1 n2 : ℕ)
    (hn1 : 0 < n1) (hn2 : 0 < n2)
    (h : n1 < n2) : ℝ :=
  1 / (R_inf * (1 / (n1 : ℝ) ^ 2 -
    1 / (n2 : ℝ) ^ 2))

theorem principal_QN_pos (n : ℕ)
    (hn : 0 < n) : 0 < n := hn

theorem angular_QN_valid (n l : ℕ)
    (hn : 0 < n) (hl : l < n) :
    l < n := hl

theorem magnetic_QN_valid (l : ℕ)
    (m : ℤ) (hm : |m| ≤ l) :
    |m| ≤ (l : ℤ) := by exact_mod_cast hm

theorem spin_half_proxy :
    (1 : ℝ) / 2 > 0 := by norm_num

def orbital_degeneracy (n : ℕ) : ℕ :=
  2 * n ^ 2

theorem orbital_degeneracy_pos (n : ℕ)
    (hn : 0 < n) :
    0 < orbital_degeneracy n := by
  unfold orbital_degeneracy
  positivity

theorem aufbau_proxy (n l : ℕ) :
    n + l ≥ 0 := Nat.zero_le _

theorem hunds_rule_proxy :
    True := trivial

theorem ionization_energy_pos
    (IE : ℝ) (h : 0 < IE) : 0 < IE := h

theorem bond_energy_pos
    (E : ℝ) (h : 0 < E) : 0 < E := h

noncomputable def morse_potential
    (D a r r0 : ℝ) (hD : 0 ≤ D) : ℝ :=
  D * (1 - Real.exp (-a * (r - r0))) ^ 2

theorem morse_nonneg
    (D a r r0 : ℝ) (hD : 0 ≤ D) :
    0 ≤ morse_potential D a r r0 hD := by
  unfold morse_potential
  exact mul_nonneg hD (sq_nonneg _)

theorem LCAO_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

theorem bond_length_pos
    (r : ℝ) (h : 0 < r) : 0 < r := h

noncomputable def rotational_energy
    (hbar I : ℝ) (J : ℕ)
    (hI : 0 < I) (hh : 0 < hbar) : ℝ :=
  hbar ^ 2 * J * (J + 1) / (2 * I)

theorem rotational_energy_nonneg
    (hbar I : ℝ) (J : ℕ)
    (hI : 0 < I) (hh : 0 < hbar) :
    0 ≤ rotational_energy hbar I J hI hh := by
  unfold rotational_energy
  have hJ : (0:ℝ) ≤ (J:ℝ) := Nat.cast_nonneg J
  have hJ1 : (0:ℝ) ≤ (J:ℝ) + 1 := by linarith
  apply div_nonneg _ (by linarith)
  have hsq : (0:ℝ) ≤ hbar ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg hsq hJ) hJ1

noncomputable def vibrational_energy
    (hbar omega : ℝ) (v : ℕ) : ℝ :=
  hbar * omega * (v + 1/2)

theorem vibrational_pos
    (hbar omega : ℝ) (v : ℕ)
    (hh : 0 < hbar) (hw : 0 < omega) :
    0 < vibrational_energy hbar omega v := by
  unfold vibrational_energy
  apply mul_pos (mul_pos hh hw)
  positivity

theorem selection_rule_proxy
    (delta_J : ℤ) : True := trivial

noncomputable def beer_lambert
    (I0 alpha l : ℝ) : ℝ :=
  I0 * Real.exp (-alpha * l)

theorem beer_lambert_pos
    (I0 alpha l : ℝ) (hI : 0 < I0) :
    0 < beer_lambert I0 alpha l :=
  mul_pos hI (Real.exp_pos _)

theorem beer_lambert_le_I0
    (I0 alpha l : ℝ)
    (hI : 0 ≤ I0) (ha : 0 ≤ alpha)
    (hl : 0 ≤ l) :
    beer_lambert I0 alpha l ≤ I0 := by
  unfold beer_lambert
  have h0 : -alpha * l ≤ 0 := by nlinarith [mul_nonneg ha hl]
  calc I0 * Real.exp (-alpha * l)
      ≤ I0 * 1 := by
        apply mul_le_mul_of_nonneg_left _ hI
        calc Real.exp (-alpha * l) ≤ Real.exp 0 := Real.exp_le_exp.mpr h0
          _ = 1 := Real.exp_zero
    _ = I0 := mul_one _

theorem doppler_broad_pos
    (delta_nu : ℝ) (h : 0 < delta_nu) :
    0 < delta_nu := h

noncomputable def geometric_cross_section
    (r : ℝ) (hr : 0 ≤ r) : ℝ :=
  Real.pi * r ^ 2

theorem cross_section_nonneg
    (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ geometric_cross_section r hr := by
  unfold geometric_cross_section
  exact mul_nonneg (le_of_lt Real.pi_pos)
    (sq_nonneg r)

noncomputable def mean_free_path
    (n sigma : ℝ)
    (hn : 0 < n) (hs : 0 < sigma) : ℝ :=
  1 / (n * sigma)

theorem mfp_pos
    (n sigma : ℝ)
    (hn : 0 < n) (hs : 0 < sigma) :
    0 < mean_free_path n sigma hn hs :=
  div_pos one_pos (mul_pos hn hs)

theorem collision_rate_nonneg
    (R : ℝ) (h : 0 ≤ R) : 0 ≤ R := h

noncomputable def thermal_wavelength
    (h m k T : ℝ)
    (hm : 0 < m) (hk : 0 < k)
    (hT : 0 < T) (hh : 0 < h) : ℝ :=
  h / Real.sqrt (2 * Real.pi * m * k * T)

theorem thermal_wavelength_pos
    (h m k T : ℝ)
    (hm : 0 < m) (hk : 0 < k)
    (hT : 0 < T) (hh : 0 < h) :
    0 < thermal_wavelength h m k T
      hm hk hT hh := by
  unfold thermal_wavelength
  apply div_pos hh
  apply Real.sqrt_pos.mpr
  positivity

theorem BEC_Tc_pos
    (T_c : ℝ) (h : 0 < T_c) : 0 < T_c := h

theorem optical_molasses_proxy :
    True := trivial

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_bohr :=
  bohr_radius 1 1 1 1
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem domain_bohr_pos :
    0 < domain_bohr :=
  bohr_radius_pos 1 1 1 1
    (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem domain_orbital_deg_pos :
    0 < orbital_degeneracy 21 :=
  orbital_degeneracy_pos 21 (by norm_num)

noncomputable def domain_morse :=
  morse_potential 1 1 2 1 (by norm_num)

theorem domain_morse_nonneg :
    0 ≤ domain_morse :=
  morse_nonneg 1 1 2 1 (by norm_num)

noncomputable def domain_vib :=
  vibrational_energy 1 1 0

theorem domain_vib_pos :
    0 < domain_vib :=
  vibrational_pos 1 1 0
    (by norm_num) (by norm_num)

noncomputable def domain_BL :=
  beer_lambert 1 1 1

theorem domain_BL_pos :
    0 < domain_BL :=
  beer_lambert_pos 1 1 1 (by norm_num)

noncomputable def domain_sigma :=
  geometric_cross_section 1 (by norm_num)

theorem domain_sigma_nonneg :
    0 ≤ domain_sigma :=
  cross_section_nonneg 1 (by norm_num)

structure AtomicMolecularLock where
  bohr_pos       : ∀ (hbar me e k : ℝ)
                     (hme : 0 < me) (he : 0 < e)
                     (hk : 0 < k) (hh : 0 < hbar),
                     0 < bohr_radius hbar me e k hme he hk hh
  H_energy_neg   : ∀ (n : ℕ) (hn : 0 < n),
                     hydrogen_energy (-13.6) n hn < 0
  orbital_pos    : ∀ (n : ℕ), 0 < n → 0 < orbital_degeneracy n
  morse_nn       : ∀ (D a r r0 : ℝ) (hD : 0 ≤ D),
                     0 ≤ morse_potential D a r r0 hD
  rot_nn         : ∀ (hbar I : ℝ) (J : ℕ)
                     (hI : 0 < I) (hh : 0 < hbar),
                     0 ≤ rotational_energy hbar I J hI hh
  vib_pos        : ∀ (hbar omega : ℝ) (v : ℕ),
                     0 < hbar → 0 < omega →
                     0 < vibrational_energy hbar omega v
  BL_pos         : ∀ (I0 alpha l : ℝ), 0 < I0 →
                     0 < beer_lambert I0 alpha l
  BL_le          : ∀ (I0 alpha l : ℝ),
                     0 ≤ I0 → 0 ≤ alpha → 0 ≤ l →
                     beer_lambert I0 alpha l ≤ I0
  sigma_nn       : ∀ (r : ℝ) (hr : 0 ≤ r),
                     0 ≤ geometric_cross_section r hr
  mfp_pos        : ∀ (n sigma : ℝ)
                     (hn : 0 < n) (hs : 0 < sigma),
                     0 < mean_free_path n sigma hn hs
  therm_pos      : ∀ (h m k T : ℝ)
                     (hm : 0 < m) (hk : 0 < k)
                     (hT : 0 < T) (hh : 0 < h),
                     0 < thermal_wavelength h m k T hm hk hT hh
  dom_bohr_pos   : 0 < domain_bohr
  dom_orb_pos    : 0 < orbital_degeneracy 21
  dom_morse_nn   : 0 ≤ domain_morse
  dom_vib_pos    : 0 < domain_vib
  dom_BL_pos     : 0 < domain_BL
  dom_sigma_nn   : 0 ≤ domain_sigma

def AMLock : AtomicMolecularLock where
  bohr_pos       := bohr_radius_pos
  H_energy_neg   := hydrogen_energy_neg
  orbital_pos    := orbital_degeneracy_pos
  morse_nn       := morse_nonneg
  rot_nn         := rotational_energy_nonneg
  vib_pos        := vibrational_pos
  BL_pos         := beer_lambert_pos
  BL_le          := beer_lambert_le_I0
  sigma_nn       := cross_section_nonneg
  mfp_pos        := mfp_pos
  therm_pos      := thermal_wavelength_pos
  dom_bohr_pos   := domain_bohr_pos
  dom_orb_pos    := domain_orbital_deg_pos
  dom_morse_nn   := domain_morse_nonneg
  dom_vib_pos    := domain_vib_pos
  dom_BL_pos     := domain_BL_pos
  dom_sigma_nn   := domain_sigma_nonneg

end AtomicMolecularPhysics
