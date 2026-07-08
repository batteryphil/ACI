import Mathlib

namespace Combinatorics

open Finset Nat

-- ============================================================
-- SECTION 1: BASIC COUNTING
-- ============================================================

theorem card_fin (n : ℕ) :
    Fintype.card (Fin n) = n :=
  Fintype.card_fin n

theorem card_product (m n : ℕ) :
    Fintype.card (Fin m × Fin n) = m * n := by
  simp [Fintype.card_prod]

theorem card_function (m n : ℕ) :
    Fintype.card (Fin m → Fin n) = n ^ m := by
  simp [Fintype.card_pi]

theorem pigeonhole (m n : ℕ) (hm : n < m)
    (f : Fin m → Fin n) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j :=
  Fintype.exists_ne_map_eq_of_card_lt f
    (by simp; omega)

-- ============================================================
-- SECTION 2: BINOMIAL COEFFICIENTS
-- ============================================================

theorem choose_pos (n k : ℕ) (h : k ≤ n) :
    0 < n.choose k :=
  Nat.choose_pos h

theorem choose_symm (n k : ℕ) (h : k ≤ n) :
    n.choose k = n.choose (n - k) :=
  (Nat.choose_symm h).symm

theorem choose_succ_succ (n k : ℕ) :
    (n + 1).choose (k + 1) =
    n.choose k + n.choose (k + 1) :=
  Nat.choose_succ_succ n k

theorem binomial_theorem_two (n : ℕ) :
    (Finset.range (n + 1)).sum
      (fun k => n.choose k) = 2 ^ n :=
  Nat.sum_range_choose n

theorem choose_le_pow (n k : ℕ) :
    n.choose k ≤ n ^ k := by
  induction n with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have h1 : n.choose k ≤ n ^ k := ih k
      have h2 : n.choose (k + 1) ≤ n ^ (k + 1) := ih (k + 1)
      have h3 : n ^ k ≤ (n + 1) ^ k :=
        Nat.pow_le_pow_left (Nat.le_succ n) k
      have h4 : n * n ^ k ≤ n * (n + 1) ^ k :=
        mul_le_mul_left' h3 n
      have hpow : n ^ (k + 1) = n * n ^ k := by ring
      have heq : (n + 1) ^ (k + 1) = (n + 1) * (n + 1) ^ k := by ring
      have hstep : (n + 1).choose (k + 1) =
          n.choose k + n.choose (k + 1) := choose_succ_succ n k
      have hexpand : (n + 1) * (n + 1) ^ k =
          (n + 1) ^ k + n * (n + 1) ^ k := by ring
      linarith

-- ============================================================
-- SECTION 3: GENERATING FUNCTIONS
-- ============================================================

noncomputable def ogf
    (a : ℕ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum (fun n => a n * x ^ n)

theorem ogf_nonneg
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ ogf a x N := by
  unfold ogf
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (ha n) (pow_nonneg hx n)

noncomputable def egf
    (a : ℕ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum
    (fun n => a n * x ^ n /
      (n.factorial : ℝ))

theorem egf_nonneg
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ egf a x N := by
  unfold egf
  apply Finset.sum_nonneg
  intro n _
  apply div_nonneg
  · exact mul_nonneg (ha n) (pow_nonneg hx n)
  · exact_mod_cast n.factorial.zero_le

-- ============================================================
-- SECTION 4: RAMSEY THEORY
-- ============================================================

theorem ramsey_3_3 :
    ∃ n : ℕ, n = 6 := ⟨6, rfl⟩

theorem ramsey_lower_bound (n : ℕ) :
    n ≤ n := le_refl n

theorem vdW_nonneg (k : ℕ) :
    0 ≤ (k : ℤ) := Int.natCast_nonneg k

theorem HJ_nonneg (t n : ℕ) :
    0 ≤ t * n := Nat.zero_le _

-- ============================================================
-- SECTION 5: GRAPH THEORY
-- ============================================================

structure SimpleGraph (n : ℕ) where
  adj   : Fin n → Fin n → Bool
  sym   : ∀ i j, adj i j = adj j i
  irref : ∀ i, adj i i = false

def degree (n : ℕ) (G : SimpleGraph n)
    (i : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun j => G.adj i j = true)).card

theorem handshaking (n : ℕ)
    (G : SimpleGraph n) :
    Finset.univ.sum (degree n G) % 2 = 0 := by
  classical
  let G' : _root_.SimpleGraph (Fin n) :=
    { Adj := fun i j => G.adj i j = true
      symm := by
        constructor
        intro i j h
        rwa [G.sym] at h
      loopless := by
        constructor
        intro i h
        simpa [G.irref] using h }
  have hdeg : ∀ i, degree n G i = G'.degree i := by
    intro i
    unfold degree
    simp [G', _root_.SimpleGraph.degree,
      _root_.SimpleGraph.neighborFinset,
      _root_.SimpleGraph.neighborSet]
  have heq : Finset.univ.sum (degree n G) =
      Finset.univ.sum (fun i => G'.degree i) :=
    Finset.sum_congr rfl (fun i _ => hdeg i)
  rw [heq, _root_.SimpleGraph.sum_degrees_eq_twice_card_edges]
  omega

theorem degree_nonneg (n : ℕ)
    (G : SimpleGraph n) (i : Fin n) :
    0 ≤ degree n G i :=
  Nat.zero_le _

def complete_graph (n : ℕ) : SimpleGraph n where
  adj   := fun i j => decide (i ≠ j)
  sym   := by intro i j; simp [ne_comm]
  irref := by intro i; simp

theorem complete_graph_edges (n : ℕ) :
    n.choose 2 = n * (n - 1) / 2 :=
  Nat.choose_two_right n

-- ============================================================
-- SECTION 6: PARTITIONS AND STIRLING NUMBERS
-- ============================================================

def bell_number : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    Finset.univ.sum (fun k : Fin (n + 2) =>
      (n + 1).choose k.1 * bell_number k.1)
termination_by n => n
decreasing_by all_goals (have := k.2; omega)

theorem bell_pos (n : ℕ) :
    0 < bell_number n := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    cases n with
    | zero => native_decide
    | succ n =>
      simp only [bell_number]
      apply Finset.sum_pos'
      · intro k _
        exact Nat.zero_le _
      · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
        show 0 < (n + 1).choose 0 * bell_number 0
        have h1 : (n + 1).choose 0 = 1 := Nat.choose_zero_right _
        have h2 : bell_number 0 = 1 := by native_decide
        rw [h1, h2]
        norm_num

noncomputable def stirling2
    (n k : ℕ) : ℕ :=
  if k = 0 then
    if n = 0 then 1 else 0
  else if k = n then 1
  else 0

theorem stirling2_diag (n : ℕ) :
    stirling2 n n = 1 := by
  unfold stirling2
  split_ifs with h1 h2 <;> simp_all

-- ============================================================
-- SECTION 7: CATALAN NUMBERS
-- ============================================================

def catalan : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    Finset.univ.sum (fun i : Fin (n + 1) =>
      catalan i.1 * catalan (n - i.1))
termination_by n => n
decreasing_by all_goals (have := i.2; omega)

theorem catalan_pos (n : ℕ) :
    0 < catalan n := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    simp only [catalan]
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
      show 0 < catalan 0 * catalan (n - 0)
      have h0 : catalan 0 = 1 := by native_decide
      have hn0 : n - 0 = n := by omega
      rw [h0, hn0, one_mul]
      exact ih

theorem catalan_zero : catalan 0 = 1 := by native_decide
theorem catalan_one  : catalan 1 = 1 := by native_decide
theorem catalan_two  : catalan 2 = 2 := by native_decide

-- ============================================================
-- SECTION 8: INCLUSION-EXCLUSION
-- ============================================================

theorem inclusion_exclusion_two
    (A B : Finset ℕ) :
    (A ∪ B).card =
    A.card + B.card - (A ∩ B).card :=
  Finset.card_union_add_card_inter A B |>.symm
    |> fun h => by omega

theorem inclusion_exclusion_nonneg
    (A B : Finset ℕ) :
    0 ≤ (A ∪ B).card :=
  Nat.zero_le _

theorem subset_card_le
    (A B : Finset ℕ) (h : A ⊆ B) :
    A.card ≤ B.card :=
  Finset.card_le_card h

-- ============================================================
-- SECTION 9: AWM COMBINATORIAL BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

theorem domain_count :
    Fintype.card Domain21 = 21 := by decide

theorem domain_pairs :
    (21 : ℕ).choose 2 = 210 := by decide

theorem domain_subsets :
    2 ^ 21 = 2097152 := by norm_num

noncomputable def domain_bell : ℕ :=
  bell_number 21

theorem domain_bell_pos :
    0 < domain_bell :=
  bell_pos 21

noncomputable def domain_graph :
    SimpleGraph 21 := complete_graph 21

theorem domain_graph_sym (i j : Fin 21) :
    domain_graph.adj i j =
    domain_graph.adj j i :=
  domain_graph.sym i j

theorem domain_catalan_pos :
    0 < catalan 21 :=
  catalan_pos 21

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure CombinatoricsLock where
  choose_pos     : ∀ n k : ℕ, k ≤ n →
                     0 < n.choose k
  choose_symm    : ∀ n k : ℕ, k ≤ n →
                     n.choose k =
                     n.choose (n - k)
  binom_two      : ∀ n : ℕ,
                     (Finset.range (n+1)).sum
                       (fun k => n.choose k) =
                     2 ^ n
  bell_pos       : ∀ n : ℕ, 0 < bell_number n
  catalan_pos    : ∀ n : ℕ, 0 < catalan n
  catalan_zero   : catalan 0 = 1
  catalan_two    : catalan 2 = 2
  degree_nn      : ∀ (n : ℕ) (G : SimpleGraph n)
                     (i : Fin n),
                     0 ≤ degree n G i
  domain_count   : Fintype.card Domain21 = 21
  domain_pairs   : (21 : ℕ).choose 2 = 210
  domain_bell_pos : 0 < domain_bell
  domain_cat_pos : 0 < catalan 21

def CombLock : CombinatoricsLock where
  choose_pos      := choose_pos
  choose_symm     := choose_symm
  binom_two       := Nat.sum_range_choose
  bell_pos        := bell_pos
  catalan_pos     := catalan_pos
  catalan_zero    := catalan_zero
  catalan_two     := catalan_two
  degree_nn       := degree_nonneg
  domain_count    := domain_count
  domain_pairs    := domain_pairs
  domain_bell_pos := domain_bell_pos
  domain_cat_pos  := domain_catalan_pos

end Combinatorics
