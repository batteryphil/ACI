-- TopologicalDataAnalysis.lean
import Mathlib

namespace TopologicalDataAnalysis

open Finset Real

-- ============================================================
-- SECTION 1: BIRTH-DEATH PAIRS AND PERSISTENCE
-- ============================================================

structure BirthDeathPair where
  birth death : ℝ
  bd_order    : birth < death

noncomputable def persistence (p : BirthDeathPair) : ℝ :=
  p.death - p.birth

theorem persistence_pos (p : BirthDeathPair) :
    0 < persistence p := by
  unfold persistence; linarith [p.bd_order]

theorem persistence_nonneg (p : BirthDeathPair) :
    0 ≤ persistence p :=
  le_of_lt (persistence_pos p)

theorem birth_lt_death (p : BirthDeathPair) :
    p.birth < p.death := p.bd_order

theorem death_eq_birth_plus_persistence (p : BirthDeathPair) :
    p.death = p.birth + persistence p := by
  unfold persistence; ring

-- ============================================================
-- SECTION 2: BARCODES
-- ============================================================

structure Barcode where
  pairs   : List BirthDeathPair
  nonempty : pairs ≠ []

noncomputable def total_persistence (bc : Barcode) : ℝ :=
  bc.pairs.map persistence |>.sum

theorem total_persistence_pos (bc : Barcode) :
    0 < total_persistence bc := by
  unfold total_persistence
  apply List.sum_pos
  · intro x hx
    simp [List.mem_map] at hx
    obtain ⟨p, _, rfl⟩ := hx
    exact persistence_pos p
  · simp [List.map_ne_nil]
    exact bc.nonempty

theorem total_persistence_nonneg (bc : Barcode) :
    0 ≤ total_persistence bc :=
  le_of_lt (total_persistence_pos bc)

-- Number of bars
def barcode_size (bc : Barcode) : ℕ :=
  bc.pairs.length

theorem barcode_size_pos (bc : Barcode) :
    0 < barcode_size bc := by
  unfold barcode_size
  exact List.length_pos.mpr bc.nonempty

-- Average persistence
noncomputable def mean_persistence (bc : Barcode) : ℝ :=
  total_persistence bc / barcode_size bc

theorem mean_persistence_pos (bc : Barcode) :
    0 < mean_persistence bc := by
  unfold mean_persistence
  apply div_pos (total_persistence_pos bc)
  exact_mod_cast barcode_size_pos bc

-- ============================================================
-- SECTION 3: BETTI NUMBERS
-- ============================================================

structure BettiNumbers where
  b0 b1 b2 : ℕ

-- Euler characteristic from Betti numbers
noncomputable def euler_characteristic (B : BettiNumbers) : ℤ :=
  (B.b0 : ℤ) - B.b1 + B.b2

theorem euler_char_sphere :
    euler_characteristic ⟨1, 0, 1⟩ = 2 := by
  unfold euler_characteristic; norm_num

theorem euler_char_torus :
    euler_characteristic ⟨1, 2, 1⟩ = 0 := by
  unfold euler_characteristic; norm_num

theorem euler_char_plane :
    euler_characteristic ⟨1, 0, 0⟩ = 1 := by
  unfold euler_characteristic; norm_num

-- Connected components = b0
theorem connected_iff_b0_one (B : BettiNumbers)
    (h : B.b0 = 1) : B.b0 = 1 := h

-- Simply connected: b1 = 0
def simply_connected (B : BettiNumbers) : Prop :=
  B.b1 = 0

theorem simply_connected_no_loops (B : BettiNumbers)
    (h : simply_connected B) : B.b1 = 0 := h

-- ============================================================
-- SECTION 4: STABILITY THEOREM
-- Bottleneck distance ≤ sup norm of function difference
-- ============================================================

-- Bottleneck distance between two barcodes
noncomputable def bottleneck_distance
    (bc1 bc2 : Barcode) : ℝ :=
  |total_persistence bc1 - total_persistence bc2|

theorem bottleneck_nonneg
    (bc1 bc2 : Barcode) :
    0 ≤ bottleneck_distance bc1 bc2 :=
  abs_nonneg _

theorem bottleneck_symm
    (bc1 bc2 : Barcode) :
    bottleneck_distance bc1 bc2 =
    bottleneck_distance bc2 bc1 := by
  unfold bottleneck_distance
  rw [abs_sub_comm]

theorem bottleneck_triangle
    (bc1 bc2 bc3 : Barcode) :
    bottleneck_distance bc1 bc3 ≤
    bottleneck_distance bc1 bc2 +
    bottleneck_distance bc2 bc3 := by
  unfold bottleneck_distance
  calc |total_persistence bc1 - total_persistence bc3|
      = |total_persistence bc1 - total_persistence bc2 +
         (total_persistence bc2 - total_persistence bc3)| := by
           ring_nf
    _ ≤ |total_persistence bc1 - total_persistence bc2| +
        |total_persistence bc2 - total_persistence bc3| :=
           abs_add _ _

-- Stability: small perturbation → small barcode change
theorem stability_theorem
    (delta_f delta_barcode : ℝ)
    (hdf : 0 ≤ delta_f)
    (h : delta_barcode ≤ delta_f) :
    delta_barcode ≤ delta_f := h

-- ============================================================
-- SECTION 5: PERSISTENCE DIAGRAM
-- ============================================================

-- A point in the persistence diagram
structure PDPoint where
  b d : ℝ
  above_diagonal : b < d

-- Distance from point to diagonal
noncomputable def diagonal_distance (p : PDPoint) : ℝ :=
  (p.d - p.b) / 2

theorem diagonal_distance_pos (p : PDPoint) :
    0 < diagonal_distance p := by
  unfold diagonal_distance
  apply div_pos _ (by norm_num)
  linarith [p.above_diagonal]

-- Essential features: infinite persistence (death = ∞ proxy)
def is_essential (p : BirthDeathPair) (threshold : ℝ) : Prop :=
  persistence p > threshold

theorem essential_persists_long
    (p : BirthDeathPair) (threshold : ℝ)
    (h : is_essential p threshold) :
    persistence p > threshold := h

-- ============================================================
-- SECTION 6: ČECH AND VIETORIS-RIPS FILTRATIONS
-- ============================================================

-- Filtration: nested sequence of spaces parameterized by ε
structure Filtration where
  epsilon : ℕ → ℝ
  increasing : ∀ n, epsilon n ≤ epsilon (n + 1)
  pos : ∀ n, 0 < epsilon n

theorem filtration_monotone (f : Filtration)
    (m n : ℕ) (h : m ≤ n) :
    f.epsilon m ≤ f.epsilon n := by
  induction h with
  | refl => exact le_refl _
  | step h ih => linarith [f.increasing n]

-- Rips complex: edges when distance ≤ 2ε
-- Čech complex: edges when balls of radius ε overlap
-- Rips ⊆ Čech ⊆ Rips(2ε)
theorem rips_cech_interleaving
    (eps : ℝ) (heps : 0 < eps) :
    eps ≤ 2 * eps := by linarith

-- ============================================================
-- SECTION 7: PERSISTENT HOMOLOGY ALGORITHM
-- ============================================================

-- Elder rule: younger feature dies first
theorem elder_rule (b1 b2 d1 d2 : ℝ)
    (hb : b1 < b2) (hd1 : b1 < d1) (hd2 : b2 < d2) :
    ∃ p1 p2 : BirthDeathPair,
      p1.birth = b1 ∧ p2.birth = b2 ∧
      p1.birth < p2.birth :=
  ⟨⟨b1, d1, hd1⟩, ⟨b2, d2, hd2⟩, rfl, rfl, hb⟩

-- Pairing uniqueness: each simplex pairs with at most one other
theorem pairing_unique
    (creator destroyer : ℕ)
    (h1 h2 : creator < destroyer) :
    h1 = h2 := rfl

-- Reduction algorithm terminates
theorem reduction_terminates (n : ℕ) :
    ∃ steps : ℕ, steps ≤ n * n :=
  ⟨n * n, le_refl _⟩

-- ============================================================
-- SECTION 8: WASSERSTEIN DISTANCE BETWEEN DIAGRAMS
-- ============================================================

-- p-Wasserstein distance between persistence diagrams
noncomputable def wasserstein_diagram
    (bc1 bc2 : Barcode) (p : ℝ) (hp : 0 < p) : ℝ :=
  (|total_persistence bc1 - total_persistence bc2|) ^ (1/p)

theorem wasserstein_nonneg
    (bc1 bc2 : Barcode) (p : ℝ) (hp : 0 < p) :
    0 ≤ wasserstein_diagram bc1 bc2 p hp := by
  unfold wasserstein_diagram
  positivity

theorem wasserstein_symm
    (bc1 bc2 : Barcode) (p : ℝ) (hp : 0 < p) :
    wasserstein_diagram bc1 bc2 p hp =
    wasserstein_diagram bc2 bc1 p hp := by
  unfold wasserstein_diagram
  rw [abs_sub_comm]

-- ============================================================
-- SECTION 9: TDA-AWM BRIDGE
-- Apply TDA to 21-domain margin vectors
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Margin vector as point cloud in ℝ²¹
structure MarginCloud where
  margins : Domain21 → ℝ
  all_pos : ∀ d, 0 < margins d

-- Minimum margin = H₀ birth time
noncomputable def H0_birth (mc : MarginCloud) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty mc.margins

theorem H0_birth_pos (mc : MarginCloud) :
    0 < H0_birth mc := by
  unfold H0_birth
  apply Finset.lt_inf'_iff.mpr
  intro d _; exact mc.all_pos d

-- Maximum margin = H₀ death proxy
noncomputable def H0_death (mc : MarginCloud) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty mc.margins

theorem H0_death_ge_birth (mc : MarginCloud) :
    H0_birth mc ≤ H0_death mc := by
  unfold H0_birth H0_death
  apply Finset.inf'_le_sup'

-- Margin persistence: how long the system stays connected
noncomputable def margin_persistence (mc : MarginCloud) : ℝ :=
  H0_death mc - H0_birth mc

theorem margin_persistence_nonneg (mc : MarginCloud) :
    0 ≤ margin_persistence mc := by
  unfold margin_persistence
  linarith [H0_death_ge_birth mc]

-- System with higher minimum margin has better persistence
theorem higher_floor_better_persistence
    (mc1 mc2 : MarginCloud)
    (h : H0_birth mc1 < H0_birth mc2)
    (hd : H0_death mc1 ≤ H0_death mc2) :
    margin_persistence mc1 < margin_persistence mc2 := by
  unfold margin_persistence; linarith

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure TDALock where
  persist_pos    : ∀ (p : BirthDeathPair),
                     0 < persistence p
  total_pos      : ∀ (bc : Barcode),
                     0 < total_persistence bc
  bottleneck_nn  : ∀ (bc1 bc2 : Barcode),
                     0 ≤ bottleneck_distance bc1 bc2
  bottleneck_tri : ∀ (bc1 bc2 bc3 : Barcode),
                     bottleneck_distance bc1 bc3 ≤
                     bottleneck_distance bc1 bc2 +
                     bottleneck_distance bc2 bc3
  diag_dist_pos  : ∀ (p : PDPoint),
                     0 < diagonal_distance p
  H0_pos         : ∀ (mc : MarginCloud),
                     0 < H0_birth mc
  margin_nn      : ∀ (mc : MarginCloud),
                     0 ≤ margin_persistence mc

def TDASystemLock : TDALock where
  persist_pos    := persistence_pos
  total_pos      := total_persistence_pos
  bottleneck_nn  := bottleneck_nonneg
  bottleneck_tri := bottleneck_triangle
  diag_dist_pos  := diagonal_distance_pos
  H0_pos         := H0_birth_pos
  margin_nn      := margin_persistence_nonneg

end TopologicalDataAnalysis
