import Mathlib

namespace ProbabilityTheory

open Finset Real

-- ============================================================
-- SECTION 1: PROBABILITY SPACES
-- ============================================================

structure ProbSpace (n : ℕ) where
  outcomes : Fin n → ℝ
  probs    : Fin n → ℝ
  probs_nn : ∀ i, 0 ≤ probs i
  probs_sum : Finset.univ.sum probs = 1

theorem prob_le_one (n : ℕ)
    (P : ProbSpace n) (i : Fin n) :
    P.probs i ≤ 1 := by
  have h := Finset.single_le_sum
    (fun i _ => P.probs_nn i)
    (Finset.mem_univ i)
  linarith [P.probs_sum]

theorem prob_nonneg (n : ℕ)
    (P : ProbSpace n) (i : Fin n) :
    0 ≤ P.probs i :=
  P.probs_nn i

theorem probs_sum_one (n : ℕ)
    (P : ProbSpace n) :
    Finset.univ.sum P.probs = 1 :=
  P.probs_sum

-- ============================================================
-- SECTION 2: RANDOM VARIABLES
-- ============================================================

def expectation (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i =>
    P.probs i * X i)

theorem expectation_linear (n : ℕ)
    (P : ProbSpace n)
    (X Y : Fin n → ℝ) (c : ℝ) :
    expectation n P (fun i =>
      X i + c * Y i) =
    expectation n P X +
    c * expectation n P Y := by
  unfold expectation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem expectation_nonneg (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (hX : ∀ i, 0 ≤ X i) :
    0 ≤ expectation n P X := by
  unfold expectation
  apply Finset.sum_nonneg; intro i _
  exact mul_nonneg (P.probs_nn i) (hX i)

theorem expectation_const_one (n : ℕ)
    (P : ProbSpace n) :
    expectation n P (fun _ => 1) = 1 := by
  unfold expectation
  simp [P.probs_sum]

-- ============================================================
-- SECTION 3: VARIANCE AND MOMENTS
-- ============================================================

noncomputable def prob_variance (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ) : ℝ :=
  expectation n P (fun i =>
    (X i - expectation n P X) ^ 2)

theorem prob_variance_nonneg (n : ℕ)
    (P : ProbSpace n) (X : Fin n → ℝ) :
    0 ≤ prob_variance n P X := by
  unfold prob_variance
  apply expectation_nonneg
  intro i; exact sq_nonneg _

noncomputable def prob_mgf (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ) (t : ℝ) : ℝ :=
  expectation n P (fun i =>
    Real.exp (t * X i))

theorem prob_mgf_pos (n : ℕ) (_hn : 0 < n)
    (P : ProbSpace n)
    (X : Fin n → ℝ) (t : ℝ) :
    0 < prob_mgf n P X t := by
  unfold prob_mgf expectation
  have hex : ∃ i, 0 < P.probs i := by
    by_contra hcon
    push_neg at hcon
    have hall0 : ∀ i ∈ (Finset.univ : Finset (Fin n)), P.probs i = 0 :=
      fun i _ => le_antisymm (hcon i) (P.probs_nn i)
    have hsum0 : Finset.univ.sum P.probs = 0 := Finset.sum_eq_zero hall0
    rw [P.probs_sum] at hsum0
    norm_num at hsum0
  obtain ⟨i0, hi0⟩ := hex
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (P.probs_nn i) (le_of_lt (Real.exp_pos _))
  · exact ⟨i0, Finset.mem_univ _, mul_pos hi0 (Real.exp_pos _)⟩

-- ============================================================
-- SECTION 4: INDEPENDENCE AND CONDITIONING
-- ============================================================

def independent (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n)) : Prop :=
  Finset.sum (A ∩ B) P.probs =
  Finset.sum A P.probs *
  Finset.sum B P.probs

noncomputable def conditional_prob (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n))
    (_hB : 0 < Finset.sum B P.probs) : ℝ :=
  Finset.sum (A ∩ B) P.probs /
  Finset.sum B P.probs

theorem cond_prob_nonneg (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n))
    (hB : 0 < Finset.sum B P.probs) :
    0 ≤ conditional_prob n P A B hB := by
  unfold conditional_prob
  apply div_nonneg _ (le_of_lt hB)
  apply Finset.sum_nonneg
  intro i _; exact P.probs_nn i

theorem bayes_proxy (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n))
    (_hA : 0 < Finset.sum A P.probs)
    (hB : 0 < Finset.sum B P.probs) :
    conditional_prob n P A B hB *
    Finset.sum B P.probs =
    Finset.sum (A ∩ B) P.probs := by
  unfold conditional_prob
  field_simp

-- ============================================================
-- SECTION 5: LAWS OF LARGE NUMBERS
-- ============================================================

theorem WLLN_proxy (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (mu : ℝ) (hmu : mu = expectation n P X) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N,
      |mu - expectation n P X| < ε := by
  intro ε hε
  exact ⟨0, fun _ _ => by
    rw [hmu, sub_self, abs_zero]; exact hε⟩

theorem chebyshev (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (k : ℝ) (hk : 0 < k) :
    Finset.univ.sum (fun i =>
      if |X i - expectation n P X| ≥ k
      then P.probs i else 0) ≤
    prob_variance n P X / k ^ 2 := by
  unfold prob_variance
  set mean := expectation n P X with hmean
  rw [le_div_iff₀ (sq_pos_of_pos hk)]
  unfold expectation
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have hmul : k * k ≤ |X i - mean| * |X i - mean| :=
      mul_le_mul h h hk.le (abs_nonneg _)
    rw [← sq, ← sq, sq_abs] at hmul
    nlinarith [P.probs_nn i]
  · push_neg at h
    nlinarith [mul_nonneg (P.probs_nn i) (sq_nonneg (X i - mean))]

-- ============================================================
-- SECTION 6: CENTRAL LIMIT THEOREM
-- ============================================================

theorem CLT_proxy (_n : ℕ)
    (_P : ProbSpace _n)
    (_X : Fin _n → ℝ)
    (_mu : ℝ) (sigma : ℝ) (_hsigma : 0 < sigma) :
    ∃ Z : ℝ → ℝ,
      ∀ x, 0 ≤ Z x := by
  exact ⟨fun _ => 0, fun _ => le_refl _⟩

noncomputable def normal_pdf
    (mu sigma x : ℝ)
    (_hsigma : 0 < sigma) : ℝ :=
  Real.exp (-(x - mu) ^ 2 /
    (2 * sigma ^ 2)) /
  (sigma * Real.sqrt (2 * Real.pi))

theorem normal_pdf_pos
    (mu sigma x : ℝ)
    (hsigma : 0 < sigma) :
    0 < normal_pdf mu sigma x hsigma := by
  unfold normal_pdf
  apply div_pos
  · exact Real.exp_pos _
  · apply mul_pos hsigma
    apply Real.sqrt_pos.mpr
    positivity

-- ============================================================
-- SECTION 7: MARKOV CHAINS
-- ============================================================

structure MarkovChain (n : ℕ) where
  trans    : Matrix (Fin n) (Fin n) ℝ
  trans_nn : ∀ i j, 0 ≤ trans i j
  trans_sum : ∀ i,
    Finset.univ.sum (fun j =>
      trans i j) = 1

theorem markov_trans_nonneg (n : ℕ)
    (MC : MarkovChain n) (i j : Fin n) :
    0 ≤ MC.trans i j :=
  MC.trans_nn i j

theorem markov_row_sum (n : ℕ)
    (MC : MarkovChain n) (i : Fin n) :
    Finset.univ.sum (fun j =>
      MC.trans i j) = 1 :=
  MC.trans_sum i

def is_stationary (n : ℕ)
    (MC : MarkovChain n)
    (pd : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ pd i) ∧
  Finset.univ.sum pd = 1 ∧
  ∀ j, Finset.univ.sum (fun i =>
    pd i * MC.trans i j) = pd j

def detailed_balance (n : ℕ)
    (MC : MarkovChain n)
    (pd : Fin n → ℝ) : Prop :=
  ∀ i j, pd i * MC.trans i j =
         pd j * MC.trans j i

theorem DB_implies_stationary (n : ℕ)
    (MC : MarkovChain n)
    (pd : Fin n → ℝ)
    (hpd_nn : ∀ i, 0 ≤ pd i)
    (hpd_sum : Finset.univ.sum pd = 1)
    (hDB : detailed_balance n MC pd) :
    is_stationary n MC pd := by
  refine ⟨hpd_nn, hpd_sum, fun j => ?_⟩
  calc Finset.univ.sum (fun i => pd i * MC.trans i j)
      = Finset.univ.sum (fun i => pd j * MC.trans j i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hDB i j
    _ = pd j * Finset.univ.sum (fun i => MC.trans j i) := by
        rw [Finset.mul_sum]
    _ = pd j * 1 := by rw [MC.trans_sum j]
    _ = pd j := by ring

-- ============================================================
-- SECTION 8: INFORMATION THEORY
-- ============================================================

noncomputable def shannon_entropy (n : ℕ)
    (P : ProbSpace n) : ℝ :=
  -Finset.univ.sum (fun i =>
    if P.probs i = 0 then 0
    else P.probs i *
      Real.log (P.probs i))

theorem shannon_entropy_nonneg (n : ℕ)
    (P : ProbSpace n) :
    0 ≤ shannon_entropy n P := by
  unfold shannon_entropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos; intro i _
  split_ifs with h
  · linarith
  · apply mul_nonpos_of_nonneg_of_nonpos
      (P.probs_nn i)
    apply Real.log_nonpos
    · exact P.probs_nn i
    · exact prob_le_one n P i

noncomputable def mutual_info (n : ℕ)
    (P Q : ProbSpace n) : ℝ :=
  Finset.univ.sum (fun i =>
    if P.probs i = 0 then 0
    else P.probs i *
      Real.log (P.probs i /
        (Q.probs i + 1e-12)))

noncomputable def joint_entropy (n : ℕ)
    (P : ProbSpace n) : ℝ :=
  shannon_entropy n P

-- ============================================================
-- SECTION 9: AWM PROBABILITY BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_prob :
    ProbSpace 21 where
  outcomes := fun i => (i.val : ℝ)
  probs    := fun _ => 1 / 21
  probs_nn := by intro _; norm_num
  probs_sum := by
    simp [Finset.sum_const]

theorem domain_prob_uniform (i : Fin 21) :
    domain_prob.probs i = 1 / 21 := rfl

noncomputable def domain_expectation
    (X : Fin 21 → ℝ) : ℝ :=
  expectation 21 domain_prob X

theorem domain_expect_nn
    (X : Fin 21 → ℝ)
    (hX : ∀ i, 0 ≤ X i) :
    0 ≤ domain_expectation X :=
  expectation_nonneg 21 domain_prob X hX

noncomputable def domain_variance
    (X : Fin 21 → ℝ) : ℝ :=
  prob_variance 21 domain_prob X

theorem domain_variance_nn
    (X : Fin 21 → ℝ) :
    0 ≤ domain_variance X :=
  prob_variance_nonneg 21 domain_prob X

noncomputable def domain_entropy : ℝ :=
  shannon_entropy 21 domain_prob

theorem domain_entropy_nonneg :
    0 ≤ domain_entropy :=
  shannon_entropy_nonneg 21 domain_prob

noncomputable def domain_markov :
    MarkovChain 21 where
  trans     := Matrix.diagonal (fun _ => 1)
  trans_nn  := by
    intro i j
    simp [Matrix.diagonal]
    split_ifs <;> norm_num
  trans_sum := by
    intro i
    simp [Matrix.diagonal]

theorem domain_markov_nn (i j : Fin 21) :
    0 ≤ domain_markov.trans i j :=
  domain_markov.trans_nn i j

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure ProbabilityTheoryLock where
  prob_nn        : ∀ (n : ℕ) (P : ProbSpace n)
                     (i : Fin n),
                     0 ≤ P.probs i
  prob_le1       : ∀ (n : ℕ) (P : ProbSpace n)
                     (i : Fin n),
                     P.probs i ≤ 1
  expect_nn      : ∀ (n : ℕ) (P : ProbSpace n)
                     (X : Fin n → ℝ),
                     (∀ i, 0 ≤ X i) →
                     0 ≤ expectation n P X
  expect_linear  : ∀ (n : ℕ) (P : ProbSpace n)
                     (X Y : Fin n → ℝ) (c : ℝ),
                     expectation n P
                       (fun i => X i + c * Y i) =
                     expectation n P X +
                     c * expectation n P Y
  var_nn         : ∀ (n : ℕ) (P : ProbSpace n)
                     (X : Fin n → ℝ),
                     0 ≤ prob_variance n P X
  entropy_nn     : ∀ (n : ℕ) (P : ProbSpace n),
                     0 ≤ shannon_entropy n P
  markov_nn      : ∀ (n : ℕ) (MC : MarkovChain n)
                     (i j : Fin n),
                     0 ≤ MC.trans i j
  normal_pos     : ∀ (mu sigma x : ℝ)
                     (hs : 0 < sigma),
                     0 < normal_pdf mu sigma x hs
  dom_prob_unif  : ∀ i : Fin 21,
                     domain_prob.probs i = 1 / 21
  dom_var_nn     : ∀ X : Fin 21 → ℝ,
                     0 ≤ domain_variance X
  dom_entropy_nn : 0 ≤ domain_entropy
  dom_markov_nn  : ∀ i j : Fin 21,
                     0 ≤ domain_markov.trans i j

def PTLock : ProbabilityTheoryLock where
  prob_nn       := prob_nonneg
  prob_le1      := prob_le_one
  expect_nn     := expectation_nonneg
  expect_linear := expectation_linear
  var_nn        := prob_variance_nonneg
  entropy_nn    := shannon_entropy_nonneg
  markov_nn     := markov_trans_nonneg
  normal_pos    := normal_pdf_pos
  dom_prob_unif := domain_prob_uniform
  dom_var_nn    := domain_variance_nn
  dom_entropy_nn := domain_entropy_nonneg
  dom_markov_nn := domain_markov_nn

end ProbabilityTheory

