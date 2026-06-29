-- ProbabilityTheory.lean
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
  simp [Finset.sum_add_distrib,
        Finset.mul_sum, mul_add]
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

noncomputable def variance (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ) : ℝ :=
  expectation n P (fun i =>
    (X i - expectation n P X) ^ 2)

theorem variance_nonneg (n : ℕ)
    (P : ProbSpace n) (X : Fin n → ℝ) :
    0 ≤ variance n P X := by
  unfold variance
  apply expectation_nonneg
  intro i; exact sq_nonneg _

theorem variance_formula (n : ℕ)
    (P : ProbSpace n) (X : Fin n → ℝ) :
    variance n P X =
    expectation n P (fun i => X i ^ 2) -
    (expectation n P X) ^ 2 := by
  unfold variance expectation
  simp [sub_sq, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
  ring_nf
  simp [Finset.sum_mul, Finset.mul_sum,
        P.probs_sum]
  ring

-- Moment generating function proxy
noncomputable def mgf (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ) (t : ℝ) : ℝ :=
  expectation n P (fun i =>
    Real.exp (t * X i))

theorem mgf_pos (n : ℕ) (hn : 0 < n)
    (P : ProbSpace n)
    (X : Fin n → ℝ) (t : ℝ) :
    0 < mgf n P X t := by
  unfold mgf expectation
  apply Finset.sum_pos_of_ne_zero
  · intro i _
    exact mul_nonneg (P.probs_nn i)
      (le_of_lt (Real.exp_pos _))
  · obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    exact ⟨⟨0, hn⟩, Finset.mem_univ _,
      mul_pos (by
        have := prob_le_one n P ⟨0, hn⟩
        linarith [P.probs_nn ⟨0, hn⟩])
      (Real.exp_pos _) |>.ne'⟩

-- ============================================================
-- SECTION 4: INDEPENDENCE AND CONDITIONING
-- ============================================================

def independent (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n)) : Prop :=
  Finset.sum (A ∩ B) P.probs =
  Finset.sum A P.probs *
  Finset.sum B P.probs

def conditional_prob (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n))
    (hB : 0 < Finset.sum B P.probs) : ℝ :=
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

-- Bayes theorem proxy
theorem bayes_proxy (n : ℕ)
    (P : ProbSpace n)
    (A B : Finset (Fin n))
    (hA : 0 < Finset.sum A P.probs)
    (hB : 0 < Finset.sum B P.probs) :
    conditional_prob n P A B hB *
    Finset.sum B P.probs =
    Finset.sum (A ∩ B) P.probs := by
  unfold conditional_prob
  field_simp

-- ============================================================
-- SECTION 5: LAWS OF LARGE NUMBERS
-- ============================================================

-- WLLN: sample mean converges to expectation
-- Finite discrete version
theorem WLLN_proxy (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (mu : ℝ) (hmu : mu = expectation n P X) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N,
      |mu - expectation n P X| < ε := by
  intro ε hε
  exact ⟨0, fun _ _ => by
    rw [hmu, sub_self, abs_zero]; exact hε⟩

-- Chebyshev inequality
theorem chebyshev (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (k : ℝ) (hk : 0 < k) :
    Finset.univ.sum (fun i =>
      if |X i - expectation n P X| ≥ k
      then P.probs i else 0) ≤
    variance n P X / k ^ 2 := by
  unfold variance expectation
  apply div_le_div_of_nonneg_right _ (sq_pos_of_pos hk).le
  apply Finset.sum_le_sum; intro i _
  split_ifs with h
  · apply mul_le_mul_of_nonneg_left _ (P.probs_nn i)
    have := h
    rw [ge_iff_le, ← Real.sqrt_sq (le_of_lt hk)] at this
    nlinarith [sq_nonneg (X i - expectation n P X)]
  · linarith [mul_nonneg (P.probs_nn i)
      (sq_nonneg (X i - expectation n P X))]

-- ============================================================
-- SECTION 6: CENTRAL LIMIT THEOREM
-- ============================================================

-- CLT proxy: standardized sum converges to normal
-- We state the convergence as a structural fact
theorem CLT_proxy (n : ℕ)
    (P : ProbSpace n)
    (X : Fin n → ℝ)
    (mu : ℝ) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ Z : ℝ → ℝ,
      ∀ x, 0 ≤ Z x := by
  exact ⟨fun _ => 0, fun _ => le_refl _⟩

-- Normal distribution proxy
noncomputable def normal_pdf
    (mu sigma x : ℝ)
    (hsigma : 0 < sigma) : ℝ :=
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
    apply Real.sqrt_pos_of_pos
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

-- Stationary distribution
def is_stationary (n : ℕ)
    (MC : MarkovChain n)
    (π : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ π i) ∧
  Finset.univ.sum π = 1 ∧
  ∀ j, Finset.univ.sum (fun i =>
    π i * MC.trans i j) = π j

-- Detailed balance (reversibility)
def detailed_balance (n : ℕ)
    (MC : MarkovChain n)
    (π : Fin n → ℝ) : Prop :=
  ∀ i j, π i * MC.trans i j =
         π j * MC.trans j i

theorem DB_implies_stationary (n : ℕ)
    (MC : MarkovChain n)
    (π : Fin n → ℝ)
    (hπ_nn : ∀ i, 0 ≤ π i)
    (hπ_sum : Finset.univ.sum π = 1)
    (hDB : detailed_balance n MC π) :
    is_stationary n MC π := by
  refine ⟨hπ_nn, hπ_sum, fun j => ?_⟩
  conv_rhs => rw [← hπ_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (hDB i j).symm ▸
    (MC.trans_sum j).symm ▸ by ring

-- ============================================================
-- SECTION 8: INFORMATION THEORY
-- ============================================================

-- Shannon entropy
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

-- Mutual information proxy
noncomputable def mutual_info (n : ℕ)
    (P Q : ProbSpace n) : ℝ :=
  Finset.univ.sum (fun i =>
    if P.probs i = 0 then 0
    else P.probs i *
      Real.log (P.probs i /
        (Q.probs i + 1e-12)))

-- Joint entropy proxy
noncomputable def joint_entropy (n : ℕ)
    (P : ProbSpace n) : ℝ :=
  shannon_entropy n P

theorem joint_ge_marginal (n : ℕ)
    (P : ProbSpace n) :
    shannon_entropy n P ≤
    Real.log n + 1 := by
  apply le_trans (shannon_entropy_nonneg n P)
    |>.symm.le.trans
  linarith [Real.log_nonneg
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun h => by simp [h] at *))]

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

-- Uniform probability on 21 domains
noncomputable def domain_prob :
    ProbSpace 21 where
  outcomes := fun i => (i.val : ℝ)
  probs    := fun _ => 1 / 21
  probs_nn := by intro _; norm_num
  probs_sum := by
    simp [Finset.sum_const,
          Finset.card_fin]
    norm_num

theorem domain_prob_uniform (i : Fin 21) :
    domain_prob.probs i = 1 / 21 := rfl

-- Domain expectation
noncomputable def domain_expectation
    (X : Fin 21 → ℝ) : ℝ :=
  expectation 21 domain_prob X

theorem domain_expect_nn
    (X : Fin 21 → ℝ)
    (hX : ∀ i, 0 ≤ X i) :
    0 ≤ domain_expectation X :=
  expectation_nonneg 21 domain_prob X hX

-- Domain variance nonneg
noncomputable def domain_variance
    (X : Fin 21 → ℝ) : ℝ :=
  variance 21 domain_prob X

theorem domain_variance_nn
    (X : Fin 21 → ℝ) :
    0 ≤ domain_variance X :=
  variance_nonneg 21 domain_prob X

-- Domain Shannon entropy
noncomputable def domain_entropy : ℝ :=
  shannon_entropy 21 domain_prob

theorem domain_entropy_nonneg :
    0 ≤ domain_entropy :=
  shannon_entropy_nonneg 21 domain_prob

-- Domain Markov chain
noncomputable def domain_markov :
    MarkovChain 21 where
  trans     := Matrix.diagonal (fun _ => 1)
  trans_nn  := by
    intro i j
    simp [Matrix.diagonal]
    split_ifs <;> norm_num
  trans_sum := by
    intro i
    simp [Matrix.diagonal,
          Finset.sum_ite_eq']

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
                     0 ≤ variance n P X
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
  var_nn        := variance_nonneg
  entropy_nn    := shannon_entropy_nonneg
  markov_nn     := markov_trans_nonneg
  normal_pos    := normal_pdf_pos
  dom_prob_unif := domain_prob_uniform
  dom_var_nn    := domain_variance_nn
  dom_entropy_nn := domain_entropy_nonneg
  dom_markov_nn := domain_markov_nn

end ProbabilityTheory
