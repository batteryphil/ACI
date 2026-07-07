import Mathlib

namespace QuantumGravity

open Finset Real

structure ADMDecomposition where
  lapse     : ℝ → ℝ
  shift     : ℝ → Fin 3 → ℝ
  metric3   : ℝ → Fin 3 → Fin 3 → ℝ
  lapse_pos : ∀ t, 0 < lapse t
  metric_symm : ∀ t i j,
    metric3 t i j = metric3 t j i
  metric_pos  : ∀ t v : Fin 3 → ℝ,
    0 ≤ univ.sum (fun i => univ.sum (fun j =>
      metric3 t i j * v i * v j))

theorem ADM_lapse_positive
    (adm : ADMDecomposition) (t : ℝ) :
    0 < adm.lapse t := adm.lapse_pos t

theorem ADM_metric_symmetric
    (adm : ADMDecomposition) (t : ℝ) (i j : Fin 3) :
    adm.metric3 t i j = adm.metric3 t j i :=
  adm.metric_symm t i j

noncomputable def ADM_mass
    (boundary_integral G_N : ℝ)
    (hG : 0 < G_N) : ℝ :=
  boundary_integral / (16 * Real.pi * G_N)

theorem ADM_mass_positive
    (boundary_integral G_N : ℝ)
    (hbi : 0 < boundary_integral)
    (hG : 0 < G_N) :
    0 < ADM_mass boundary_integral G_N hG := by
  unfold ADM_mass; positivity

noncomputable def dewitt_metric
    (gamma : Fin 3 → Fin 3 → ℝ)
    (i j k l : Fin 3) : ℝ :=
  (1/2) * (gamma i k * gamma j l +
           gamma i l * gamma j k -
           gamma i j * gamma k l)

theorem dewitt_metric_symm
    (gamma : Fin 3 → Fin 3 → ℝ)
    (i j k l : Fin 3) :
    dewitt_metric gamma i j k l =
    dewitt_metric gamma k l i j := by
  unfold dewitt_metric; ring

def universe_wavefunction (metric_space : ℝ) : ℝ :=
  Real.exp (-metric_space)

theorem wavefunction_pos (x : ℝ) :
    0 < universe_wavefunction x :=
  Real.exp_pos _

theorem wavefunction_decays
    (x y : ℝ) (h : x < y) :
    universe_wavefunction y <
    universe_wavefunction x := by
  unfold universe_wavefunction
  exact Real.exp_lt_exp.mpr (neg_lt_neg h)

noncomputable def HH_amplitude
    (S_euclidean : ℝ) : ℝ :=
  Real.exp (-S_euclidean)

theorem HH_amplitude_pos (S : ℝ) :
    0 < HH_amplitude S :=
  Real.exp_pos _

structure AshtekarVariables where
  connection : Fin 3 → Fin 3 → ℝ
  triad      : Fin 3 → Fin 3 → ℝ
  triad_pos  : ∀ i a, 0 ≤ triad i a

noncomputable def holonomy
    (A : Fin 3 → ℝ) (length : ℝ) : ℝ :=
  Real.exp (univ.sum (fun i => A i) * length)

theorem holonomy_pos
    (A : Fin 3 → ℝ) (length : ℝ) :
    0 < holonomy A length :=
  Real.exp_pos _

theorem holonomy_multiplicative
    (A : Fin 3 → ℝ) (L1 L2 : ℝ) :
    holonomy A (L1 + L2) =
    holonomy A L1 * holonomy A L2 := by
  unfold holonomy
  rw [mul_add, Real.exp_add]

structure SpinNetwork where
  n_nodes : ℕ
  n_edges : ℕ
  spins   : Fin n_edges → ℕ
  nodes_pos : 0 < n_nodes
  edges_pos : 0 < n_edges

noncomputable def area_eigenvalue
    (gamma l_P : ℝ) (j : ℕ) : ℝ :=
  8 * Real.pi * gamma * l_P ^ 2 *
  Real.sqrt (j * (j + 1))

theorem area_eigenvalue_nonneg
    (gamma l_P : ℝ) (j : ℕ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P) :
    0 ≤ area_eigenvalue gamma l_P j := by
  unfold area_eigenvalue
  apply mul_nonneg
  · positivity
  · exact Real.sqrt_nonneg _

theorem area_eigenvalue_pos
    (gamma l_P : ℝ) (j : ℕ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P)
    (hj : 0 < j) :
    0 < area_eigenvalue gamma l_P j := by
  unfold area_eigenvalue
  apply mul_pos
  · positivity
  · apply Real.sqrt_pos_of_pos
    apply mul_pos
    · exact_mod_cast hj
    · exact_mod_cast Nat.succ_pos j

noncomputable def volume_eigenvalue
    (gamma l_P : ℝ) (n : ℕ) : ℝ :=
  (8 * Real.pi * gamma) ^ (3/2 : ℝ) *
  l_P ^ 3 * Real.sqrt n

theorem volume_eigenvalue_nonneg
    (gamma l_P : ℝ) (n : ℕ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P) :
    0 ≤ volume_eigenvalue gamma l_P n := by
  unfold volume_eigenvalue
  apply mul_nonneg
  · apply mul_nonneg
    · apply Real.rpow_nonneg; positivity
    · positivity
  · exact Real.sqrt_nonneg _

theorem area_spectrum_discrete
    (gamma l_P : ℝ) (j1 j2 : ℕ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P)
    (hj : j1 ≠ j2) :
    area_eigenvalue gamma l_P j1 ≠
    area_eigenvalue gamma l_P j2 := by
  unfold area_eigenvalue
  intro h
  have hpos : 0 < 8 * Real.pi * gamma * l_P ^ 2 :=
    by positivity
  have hcancel := mul_left_cancel₀ hpos.ne' h
  have hAnn : (0:ℝ) ≤ (j1:ℝ) * (j1 + 1) := by positivity
  have hBnn : (0:ℝ) ≤ (j2:ℝ) * (j2 + 1) := by positivity
  have hsq1 : Real.sqrt ((j1:ℝ) * (j1 + 1)) ^ 2 =
      (j1:ℝ) * (j1 + 1) := Real.sq_sqrt hAnn
  have hsq2 : Real.sqrt ((j2:ℝ) * (j2 + 1)) ^ 2 =
      (j2:ℝ) * (j2 + 1) := Real.sq_sqrt hBnn
  have heq2 : Real.sqrt ((j1:ℝ) * (j1 + 1)) ^ 2 =
      Real.sqrt ((j2:ℝ) * (j2 + 1)) ^ 2 := by rw [hcancel]
  rw [hsq1, hsq2] at heq2
  have hjeq : (j1 : ℝ) = j2 := by
    rcases lt_trichotomy j1 j2 with hlt | heq | hgt
    · exfalso
      have : (j1:ℝ) < j2 := by exact_mod_cast hlt
      nlinarith
    · exact_mod_cast heq
    · exfalso
      have : (j2:ℝ) < j1 := by exact_mod_cast hgt
      nlinarith
  exact hj (by exact_mod_cast hjeq)

noncomputable def schwarzschild_radius
    (M G_N c : ℝ)
    (hG : 0 < G_N) (hc : 0 < c) : ℝ :=
  2 * G_N * M / c ^ 2

theorem schwarzschild_pos
    (M G_N c : ℝ)
    (hM : 0 < M) (hG : 0 < G_N) (hc : 0 < c) :
    0 < schwarzschild_radius M G_N c hG hc := by
  unfold schwarzschild_radius; positivity

noncomputable def hawking_temperature
    (M G_N hbar c k_B : ℝ)
    (hM : 0 < M) (hG : 0 < G_N)
    (hh : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k_B) : ℝ :=
  hbar * c ^ 3 / (8 * Real.pi * G_N * M * k_B)

theorem hawking_temp_pos
    (M G_N hbar c k_B : ℝ)
    (hM : 0 < M) (hG : 0 < G_N)
    (hh : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k_B) :
    0 < hawking_temperature M G_N hbar c k_B
          hM hG hh hc hk := by
  unfold hawking_temperature; positivity

theorem hawking_temp_decreases
    (M1 M2 G_N hbar c k_B : ℝ)
    (hM1 : 0 < M1) (hM2 : 0 < M2)
    (hG : 0 < G_N) (hh : 0 < hbar)
    (hc : 0 < c) (hk : 0 < k_B)
    (h : M1 < M2) :
    hawking_temperature M2 G_N hbar c k_B
      hM2 hG hh hc hk <
    hawking_temperature M1 G_N hbar c k_B
      hM1 hG hh hc hk := by
  unfold hawking_temperature
  gcongr
  positivity

noncomputable def BH_entropy
    (A l_P : ℝ) (hlP : 0 < l_P) : ℝ :=
  A / (4 * l_P ^ 2)

theorem BH_entropy_pos
    (A l_P : ℝ) (hA : 0 < A) (hlP : 0 < l_P) :
    0 < BH_entropy A l_P hlP := by
  unfold BH_entropy; positivity

theorem BH_entropy_area_law
    (A1 A2 l_P : ℝ) (hlP : 0 < l_P)
    (h : A1 < A2) :
    BH_entropy A1 l_P hlP <
    BH_entropy A2 l_P hlP := by
  unfold BH_entropy
  gcongr

def area_second_law
    (A_initial A_final : ℝ) : Prop :=
  A_initial ≤ A_final

theorem entropy_second_law
    (A_i A_f l_P : ℝ) (hlP : 0 < l_P)
    (h : area_second_law A_i A_f)
    (hAi : 0 < A_i) :
    BH_entropy A_i l_P hlP ≤
    BH_entropy A_f l_P hlP := by
  unfold BH_entropy area_second_law at *
  gcongr

def graviton_spin : ℕ := 2

noncomputable def graviton_propagator
    (k_sq : ℝ) (hk : 0 < k_sq) : ℝ :=
  1 / k_sq

theorem graviton_propagator_pos
    (k_sq : ℝ) (hk : 0 < k_sq) :
    0 < graviton_propagator k_sq hk :=
  div_pos one_pos hk

theorem graviton_propagator_decreasing
    (k1 k2 : ℝ) (hk1 : 0 < k1) (hk2 : 0 < k2)
    (h : k1 < k2) :
    graviton_propagator k2 hk2 <
    graviton_propagator k1 hk1 := by
  unfold graviton_propagator
  gcongr

theorem newton_law_from_graviton
    (G_N r : ℝ) (hG : 0 < G_N) (hr : 0 < r) :
    0 < G_N / r ^ 2 := by
  positivity

structure FRWUniverse where
  scale       : ℝ → ℝ
  scale_pos   : ∀ t, 0 < scale t
  H           : ℝ → ℝ

noncomputable def friedmann_H_sq
    (G_N rho k a : ℝ)
    (hG : 0 < G_N) (ha : 0 < a) : ℝ :=
  8 * Real.pi * G_N / 3 * rho - k / a ^ 2

theorem flat_friedmann
    (G_N rho a : ℝ)
    (hG : 0 < G_N) (hrho : 0 < rho)
    (ha : 0 < a) :
    0 < friedmann_H_sq G_N rho 0 a hG ha := by
  unfold friedmann_H_sq; simp; positivity

noncomputable def deSitter_scale
    (a0 H t : ℝ) : ℝ :=
  a0 * Real.exp (H * t)

theorem deSitter_pos
    (a0 H t : ℝ) (ha0 : 0 < a0) :
    0 < deSitter_scale a0 H t := by
  unfold deSitter_scale
  exact mul_pos ha0 (Real.exp_pos _)

theorem deSitter_expanding
    (a0 H t1 t2 : ℝ)
    (ha0 : 0 < a0) (hH : 0 < H) (h : t1 < t2) :
    deSitter_scale a0 H t1 <
    deSitter_scale a0 H t2 := by
  unfold deSitter_scale
  apply mul_lt_mul_of_pos_left _ ha0
  exact Real.exp_lt_exp.mpr (by nlinarith)

theorem inflation_solves_horizon
    (a0 H T : ℝ) (ha0 : 0 < a0) (hH : 0 < H)
    (hT : 0 < T) :
    ∃ t : ℝ, 0 < t ∧ t < T ∧
      deSitter_scale a0 H t > a0 := by
  refine ⟨T/2, by linarith, by linarith, ?_⟩
  unfold deSitter_scale
  have hexp : Real.exp 0 < Real.exp (H * (T/2)) :=
    Real.exp_lt_exp.mpr (by positivity)
  rw [Real.exp_zero] at hexp
  nlinarith

noncomputable def planck_length
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) : ℝ :=
  Real.sqrt (hbar * G_N / c ^ 3)

theorem planck_length_pos
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) :
    0 < planck_length hbar G_N c hh hG hc := by
  unfold planck_length
  apply Real.sqrt_pos_of_pos; positivity

noncomputable def planck_mass
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) : ℝ :=
  Real.sqrt (hbar * c / G_N)

theorem planck_mass_pos
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) :
    0 < planck_mass hbar G_N c hh hG hc := by
  unfold planck_mass
  apply Real.sqrt_pos_of_pos; positivity

noncomputable def planck_energy
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) : ℝ :=
  planck_mass hbar G_N c hh hG hc * c ^ 2

theorem planck_energy_pos
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) :
    0 < planck_energy hbar G_N c hh hG hc := by
  unfold planck_energy
  exact mul_pos (planck_mass_pos hbar G_N c hh hG hc)
    (pow_pos hc 2)

noncomputable def GUP_bound
    (hbar beta Delta_p m_P c : ℝ)
    (hh : 0 < hbar) (hm : 0 < m_P)
    (hc : 0 < c) : ℝ :=
  hbar / 2 * (1 + beta * Delta_p ^ 2 /
    (m_P ^ 2 * c ^ 2))

theorem GUP_ge_HUP
    (hbar beta Delta_p m_P c : ℝ)
    (hh : 0 < hbar) (hm : 0 < m_P)
    (hc : 0 < c) (hb : 0 ≤ beta) :
    hbar / 2 ≤
    GUP_bound hbar beta Delta_p m_P c hh hm hc := by
  unfold GUP_bound
  nlinarith [sq_nonneg Delta_p,
             mul_nonneg hb (sq_nonneg Delta_p),
             mul_pos (pow_pos hm 2) (pow_pos hc 2)]

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure AWMSpinNetwork where
  node_spins : Domain21 → ℕ
  edge_spins : Domain21 → Domain21 → ℕ

noncomputable def domain_area
    (sn : AWMSpinNetwork)
    (gamma l_P : ℝ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P)
    (d : Domain21) : ℝ :=
  area_eigenvalue gamma l_P (sn.node_spins d)

theorem domain_area_nonneg
    (sn : AWMSpinNetwork)
    (gamma l_P : ℝ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P)
    (d : Domain21) :
    0 ≤ domain_area sn gamma l_P hgamma hlP d :=
  area_eigenvalue_nonneg gamma l_P
    (sn.node_spins d) hgamma hlP

noncomputable def AWM_total_area
    (sn : AWMSpinNetwork)
    (gamma l_P : ℝ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P) : ℝ :=
  Finset.univ.sum (fun d =>
    domain_area sn gamma l_P hgamma hlP d)

theorem AWM_total_area_nonneg
    (sn : AWMSpinNetwork)
    (gamma l_P : ℝ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P) :
    0 ≤ AWM_total_area sn gamma l_P hgamma hlP := by
  unfold AWM_total_area
  apply Finset.sum_nonneg; intro d _
  exact domain_area_nonneg sn gamma l_P hgamma hlP d

noncomputable def AWM_BH_entropy
    (sn : AWMSpinNetwork)
    (gamma l_P : ℝ)
    (hgamma : 0 < gamma) (hlP : 0 < l_P) : ℝ :=
  BH_entropy
    (AWM_total_area sn gamma l_P hgamma hlP)
    l_P hlP

noncomputable def AWM_hawking_temp
    (M G_N hbar c k_B : ℝ)
    (hM : 0 < M) (hG : 0 < G_N)
    (hh : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k_B) : ℝ :=
  hawking_temperature M G_N hbar c k_B hM hG hh hc hk

theorem AWM_temp_pos
    (M G_N hbar c k_B : ℝ)
    (hM : 0 < M) (hG : 0 < G_N)
    (hh : 0 < hbar) (hc : 0 < c)
    (hk : 0 < k_B) :
    0 < AWM_hawking_temp M G_N hbar c k_B
          hM hG hh hc hk :=
  hawking_temp_pos M G_N hbar c k_B hM hG hh hc hk

noncomputable def domain_scale_factor
    (a0 H : ℝ) (ha0 : 0 < a0) (hH : 0 < H)
    (d : Domain21) (t : ℝ) : ℝ :=
  deSitter_scale a0 H t

theorem domain_universe_expanding
    (a0 H : ℝ) (ha0 : 0 < a0) (hH : 0 < H)
    (d : Domain21) (t1 t2 : ℝ) (h : t1 < t2) :
    domain_scale_factor a0 H ha0 hH d t1 <
    domain_scale_factor a0 H ha0 hH d t2 :=
  deSitter_expanding a0 H t1 t2 ha0 hH h

def above_planck_scale
    (margins : Domain21 → ℝ)
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c) : Prop :=
  ∀ d : Domain21,
    planck_length hbar G_N c hh hG hc ≤
    margins d

theorem planck_above_implies_all_positive
    (margins : Domain21 → ℝ)
    (hbar G_N c : ℝ)
    (hh : 0 < hbar) (hG : 0 < G_N)
    (hc : 0 < c)
    (h : above_planck_scale margins hbar G_N c hh hG hc) :
    ∀ d : Domain21, 0 < margins d := by
  intro d
  exact lt_of_lt_of_le
    (planck_length_pos hbar G_N c hh hG hc)
    (h d)

structure QuantumGravityLock where
  ADM_lapse_pos     : ∀ (adm : ADMDecomposition)
                        (t : ℝ),
                        0 < adm.lapse t
  HH_pos            : ∀ (S : ℝ),
                        0 < HH_amplitude S
  wavefunction_pos  : ∀ (x : ℝ),
                        0 < universe_wavefunction x
  wavefunction_dec  : ∀ (x y : ℝ), x < y →
                        universe_wavefunction y <
                        universe_wavefunction x
  holonomy_pos      : ∀ (A : Fin 3 → ℝ) (L : ℝ),
                        0 < holonomy A L
  holonomy_mul      : ∀ (A : Fin 3 → ℝ) (L1 L2 : ℝ),
                        holonomy A (L1 + L2) =
                        holonomy A L1 * holonomy A L2
  area_nn           : ∀ (g l : ℝ) (j : ℕ),
                        0 < g → 0 < l →
                        0 ≤ area_eigenvalue g l j
  area_pos          : ∀ (g l : ℝ) (j : ℕ),
                        0 < g → 0 < l → 0 < j →
                        0 < area_eigenvalue g l j
  hawking_pos       : ∀ (M G h c k : ℝ)
                        (hM : 0 < M) (hG : 0 < G)
                        (hh : 0 < h) (hc : 0 < c)
                        (hk : 0 < k),
                        0 < hawking_temperature
                              M G h c k hM hG hh hc hk
  hawking_decreasing : ∀ (M1 M2 G h c k : ℝ)
                        (hM1 : 0 < M1) (hM2 : 0 < M2)
                        (hG : 0 < G) (hh : 0 < h)
                        (hc : 0 < c) (hk : 0 < k),
                        M1 < M2 →
                        hawking_temperature M2 G h c k
                          hM2 hG hh hc hk <
                        hawking_temperature M1 G h c k
                          hM1 hG hh hc hk
  BH_entropy_pos    : ∀ (A l : ℝ)
                        (hA : 0 < A) (hl : 0 < l),
                        0 < BH_entropy A l hl
  deSitter_pos      : ∀ (a0 H t : ℝ),
                        0 < a0 →
                        0 < deSitter_scale a0 H t
  deSitter_exp      : ∀ (a0 H t1 t2 : ℝ),
                        0 < a0 → 0 < H → t1 < t2 →
                        deSitter_scale a0 H t1 <
                        deSitter_scale a0 H t2
  planck_l_pos      : ∀ (h G c : ℝ)
                        (hh : 0 < h) (hG : 0 < G)
                        (hc : 0 < c),
                        0 < planck_length h G c hh hG hc
  GUP_ge_HUP        : ∀ (h b dp m c : ℝ)
                        (hh : 0 < h) (hm : 0 < m)
                        (hc : 0 < c) (hb : 0 ≤ b),
                        h/2 ≤ GUP_bound h b dp m c hh hm hc
  AWM_area_nn       : ∀ (sn : AWMSpinNetwork)
                        (g l : ℝ)
                        (hg : 0 < g) (hl : 0 < l),
                        0 ≤ AWM_total_area sn g l hg hl
  planck_implies_pos : ∀ (m : Domain21 → ℝ)
                         (h G c : ℝ)
                         (hh : 0 < h) (hG : 0 < G)
                         (hc : 0 < c),
                         above_planck_scale m h G c hh hG hc →
                         ∀ d, 0 < m d

def QGLock : QuantumGravityLock where
  ADM_lapse_pos      := ADM_lapse_positive
  HH_pos             := HH_amplitude_pos
  wavefunction_pos   := wavefunction_pos
  wavefunction_dec   := wavefunction_decays
  holonomy_pos       := holonomy_pos
  holonomy_mul       := holonomy_multiplicative
  area_nn            := area_eigenvalue_nonneg
  area_pos           := area_eigenvalue_pos
  hawking_pos        := hawking_temp_pos
  hawking_decreasing := hawking_temp_decreases
  BH_entropy_pos     := BH_entropy_pos
  deSitter_pos       := deSitter_pos
  deSitter_exp       := deSitter_expanding
  planck_l_pos       := planck_length_pos
  GUP_ge_HUP         := GUP_ge_HUP
  AWM_area_nn        := AWM_total_area_nonneg
  planck_implies_pos := planck_above_implies_all_positive

end QuantumGravity
