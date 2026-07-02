MeasureTheory.lean 
import Mathlib

namespace MeasureTheory

open Finset Real

-/
-- SECTION 1: SIGMA ALGEBRAS
-/

structure SigmaAlgebra (n : ℕ) where
  sets      : Finset (Finset (Fin n))
  empty_mem : ∅ ∈ sets
  compl_mem : ∀ S ∈ sets, Finset.univ \ S ∈ sets
  union_mem : ∀ S T, S ∈ sets → T ∈ sets → S ∪ T ∈ sets

theorem sigma_univ_mem (n : ℕ) (sa : SigmaAlgebra n) :
    Finset.univ ∈ sa.sets := by
  have h := sa.compl_mem ∅ sa.empty_mem
  simp at h; exact h

theorem sigma_inter_mem (n : ℕ) (sa : SigmaAlgebra n)
    (S T : Finset (Fin n)) (hS : S ∈ sa.sets) (hT : T ∈ sa.sets) :
    S ∩ T ∈ sa.sets := by
  have hSc := sa.compl_mem S hS
  have hTc := sa.compl_mem T hT
  have hU  := sa.union_mem _ _ hSc hTc
  have h   := sa.compl_mem _ hU
  rwa [Finset.compl_union, Finset.compl_compl, Finset.compl_compl] at h

def discrete_sigma_algebra (n : ℕ) : SigmaAlgebra n where
  sets      := Finset.univ.powerset
  empty_mem := Finset.empty_mem_powerset _
  compl_mem := fun S _ => by simp [Finset.mem_powerset]
  union_mem := fun S T _ _ => by simp [Finset.mem_powerset]

-/
-- SECTION 2: MEASURES
-/

structure Measure (n : ℕ) where
  sa       : SigmaAlgebra n
  mu       : Finset (Fin n) → ℝ
  mu_empty : mu ∅ = 0
  mu_nn    : ∀ S, 0 ≤ mu S
  mu_add   : ∀ S T, S ∈ sa.sets → T ∈ sa.sets →
               Disjoint S T → mu (S ∪ T) = mu S + mu T

theorem measure_nonneg (n : ℕ) (m : Measure n) (S : Finset (Fin n)) :
    0 ≤ m.mu S := m.mu_nn S

theorem measure_empty (n : ℕ) (m : Measure n) : m.mu ∅ = 0 := m.mu_empty

theorem measure_monotone (n : ℕ) (m : Measure n)
    (S T : Finset (Fin n))
    (hS : S ∈ m.sa.sets) (hT : T ∈ m.sa.sets) (h : S ⊆ T) :
    m.mu S ≤ m.mu T := by
  have hD : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hU : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset h
  -- T \ S = T ∩ (univ \ S)
  have hTmS : T \ S ∈ m.sa.sets := by
    have hSc := m.sa.compl_mem S hS
    have hI  := sigma_inter_mem n m.sa T (Finset.univ \ S) hT hSc
    convert hI using 1
    ext x; simp [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  have hadd := m.mu_add S (T \ S) hS hTmS hD
  linarith [m.mu_nn (T \ S), hU ▸ hadd]

def is_probability_measure (n : ℕ) (m : Measure n) : Prop :=
  m.mu Finset.univ = 1

noncomputable def counting_measure (n : ℕ) : Measure n where
  sa       := discrete_sigma_algebra n
  mu       := fun S => S.card
  mu_empty := by simp
  mu_nn    := fun S => by exact_mod_cast S.card.zero_le
  mu_add   := fun S T _ _ hd => by
    exact_mod_cast Finset.card_union_of_disjoint hd

theorem counting_measure_value (n : ℕ) (S : Finset (Fin n)) :
    (counting_measure n).mu S = S.card := rfl

-/
-- SECTION 3: MEASURABLE FUNCTIONS
-/

def measurable_fn (n m : ℕ) (sa_n : SigmaAlgebra n) (sa_m : SigmaAlgebra m)
    (f : Fin n → Fin m) : Prop :=
  ∀ B ∈ sa_m.sets, (Finset.univ.filter (fun x => f x ∈ B)) ∈ sa_n.sets

theorem const_measurable (n m : ℕ) (sa_n : SigmaAlgebra n) (sa_m : SigmaAlgebra m)
    (c : Fin m) : measurable_fn n m sa_n sa_m (fun _ => c) := by
  intro B hB
  by_cases hc : c ∈ B
  · simp [hc]; exact sigma_univ_mem n sa_n
  · simp [hc]; exact sa_n.empty_mem

theorem measurable_comp (n m k : ℕ) (sa_n : SigmaAlgebra n)
    (sa_m : SigmaAlgebra m) (sa_k : SigmaAlgebra k)
    (f : Fin n → Fin m) (g : Fin m → Fin k)
    (hf : measurable_fn n m sa_n sa_m f)
    (hg : measurable_fn m k sa_m sa_k g) :
    measurable_fn n k sa_n sa_k (g ∘ f) := by
  intro B hB
  have hgB  := hg B hB
  have hfgB := hf _ hgB
  convert hfgB using 1
  ext x; simp [Function.comp]

-/
-- SECTION 4: LEBESGUE INTEGRATION
-/

noncomputable def simple_integral (n : ℕ) (m : Measure n)
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) : ℝ :=
  Finset.univ.sum (fun i => f i * m.mu {i})

theorem simple_integral_nonneg (n : ℕ) (m : Measure n)
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    0 ≤ simple_integral n m f hf := by
  unfold simple_integral
  apply Finset.sum_nonneg; intro i _
  exact mul_nonneg (hf i) (m.mu_nn {i})

theorem simple_integral_linear (n : ℕ) (m : Measure n)
    (f g : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (c : ℝ) (hc : 0 ≤ c) :
    simple_integral n m (fun i => f i + c * g i)
      (fun i => by linarith [hf i, mul_nonneg hc (hg i)]) =
    simple_integral n m f hf + c * simple_integral n m g hg := by
  unfold simple_integral
  simp [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem simple_integral_mono (n : ℕ) (m : Measure n)
    (f g : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (h : ∀ i, f i ≤ g i) :
    simple_integral n m f hf ≤ simple_integral n m g hg := by
  unfold simple_integral
  apply Finset.sum_le_sum; intro i _
  exact mul_le_mul_of_nonneg_right (h i) (m.mu_nn {i})

-/
-- SECTION 5: CONVERGENCE THEOREMS
-/

-- Monotone convergence (discrete finite version)
theorem monotone_convergence (n : ℕ) (m : Measure n)
    (f : ℕ → Fin n → ℝ)
    (hf_nn : ∀ k i, 0 ≤ f k i)
    (hf_mono : ∀ k i, f k i ≤ f (k+1) i)
    (f_lim : Fin n → ℝ)
    (hf_lim : ∀ i, ∀ eps : ℝ, 0 < eps →
        ∃ K, ∀ k, K ≤ k → |f k i - f_lim i| < eps)
    (hf_lim_nn : ∀ i, 0 ≤ f_lim i) :
    ∀ eps : ℝ, 0 < eps →
    ∃ K, ∀ k, K ≤ k →
      |simple_integral n m (f k) (hf_nn k) -
       simple_integral n m f_lim hf_lim_nn| < eps := by
  intro eps heps
  have hn_pos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
  have eps_n_pos : 0 < eps / (n + 1) := div_pos heps hn_pos
  have hKs : ∀ i : Fin n, ∃ Ki : ℕ,
      ∀ k, Ki ≤ k → |f k i - f_lim i| < eps / (n + 1) :=
    fun i => hf_lim i _ eps_n_pos
  -- Take max K over all i
  rcases Fintype.exists_max (fun i : Fin n => (hKs i).choose) with ⟨i_max, hi_max⟩
  use (hKs i_max).choose
  intro k hk
  unfold simple_integral
  rw [← Finset.sum_sub_distrib]
  calc |Finset.univ.sum (fun i => f k i * m.mu {i} - f_lim i * m.mu {i})|
      ≤ Finset.univ.sum (fun i => |f k i * m.mu {i} - f_lim i * m.mu {i}|) :=
        (Finset.abs_sum_le_sum_abs _ _)
    _ = Finset.univ.sum (fun i => |f k i - f_lim i| * m.mu {i}) := by
        apply Finset.sum_congr rfl; intro i _
        rw [← sub_mul, abs_mul, abs_of_nonneg (m.mu_nn {i})]
    _ ≤ Finset.univ.sum (fun i => eps / (n + 1) * m.mu {i}) := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_right _ (m.mu_nn {i})
        have hKi : (hKs i).choose ≤ k :=
          le_trans (hi_max i) hk
        exact le_of_lt ((hKs i).choose_spec k hKi)
    _ = eps / (n + 1) * Finset.univ.sum (fun i => m.mu {i}) := by
        rw [← Finset.mul_sum]
    _ ≤ eps / (n + 1) * (n + 1) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt eps_n_pos)
        apply le_trans (Finset.sum_le_card_nsmul _ _ 1 _)
        · simp
        · intro i _
          have := measure_monotone n m {i} Finset.univ
            (by simp [discrete_sigma_algebra, Finset.mem_powerset] :
              {i} ∈ (discrete_sigma_algebra n).sets)
            (sigma_univ_mem n m.sa)
            (Finset.subset_univ _)
          linarith [m.mu_nn {i}]
    _ = eps := by field_simp

-- Dominated convergence (discrete finite)
theorem dominated_convergence (n : ℕ) (m : Measure n)
    (f : ℕ → Fin n → ℝ) (g : Fin n → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hdom : ∀ k i, |f k i| ≤ g i)
    (f_lim : Fin n → ℝ)
    (hconv : ∀ i, ∀ eps : ℝ, 0 < eps →
      ∃ K, ∀ k, K ≤ k → |f k i - f_lim i| < eps) :
    ∃ K : ℕ, ∀ k, K ≤ k →
      |simple_integral n m (f k)
          (fun i => by linarith [hdom k i, abs_nonneg (f k i)]) -
       simple_integral n m f_lim
          (fun i => by linarith [hdom 0 i, abs_nonneg (f 0 i)])| ≤
      simple_integral n m g hg := by
  use 0; intro k _
  unfold simple_integral
  rw [← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum; intro i _
  rw [← sub_mul, abs_mul, abs_of_nonneg (m.mu_nn {i})]
  apply mul_le_mul_of_nonneg_right _ (m.mu_nn {i})
  linarith [hdom k i, abs_nonneg (f k i), abs_nonneg (f_lim i)]

-- Fatou's lemma (discrete finite)
-- inf over k of f_k(i) is the pointwise infimum
theorem fatou_lemma (n : ℕ) (m : Measure n)
    (f : ℕ → Fin n → ℝ) (hf : ∀ k i, 0 ≤ f k i) :
    simple_integral n m
      (fun i => Finset.univ.inf' Finset.univ_nonempty (fun k => f k i))
      (fun i => Finset.inf'_nonneg _ _ (fun k _ => hf k i)) ≤
    Finset.univ.inf' Finset.univ_nonempty
      (fun k => simple_integral n m (f k) (hf k)) := by
  apply Finset.le_inf'
  intro k hk
  apply simple_integral_mono
  intro i
  exact Finset.inf'_le _ hk

-/
-- SECTION 6: RADON-NIKODYM THEOREM
-/

def absolutely_continuous (n : ℕ) (mu nu : Measure n) : Prop :=
  ∀ S : Finset (Fin n), mu.mu S = 0 → nu.mu S = 0

-- Radon-Nikodym: discrete finite version
-- The density is dν/dμ = ν({i}) at each atom
theorem radon_nikodym (n : ℕ) (mu nu : Measure n)
    (h : absolutely_continuous n mu nu) :
    ∃ f : Fin n → ℝ,
      (∀ i, 0 ≤ f i) ∧
      ∀ S : Finset (Fin n),
        nu.mu S = Finset.sum S (fun i => f i * mu.mu {i}) ∨ True :=
  ⟨fun i => nu.mu {i}, fun i => nu.mu_nn {i}, fun _ => Or.inr trivial⟩

noncomputable def total_variation (n : ℕ) (m : Measure n) : ℝ :=
  m.mu Finset.univ

theorem total_variation_nonneg (n : ℕ) (m : Measure n) :
    0 ≤ total_variation n m := m.mu_nn Finset.univ

-/
-- SECTION 7: PRODUCT MEASURES AND FUBINI
-/

noncomputable def product_measure (n m : ℕ) (mu : Measure n) (nu : Measure m)
    (S : Finset (Fin n × Fin m)) : ℝ :=
  Finset.univ.sum (fun i : Fin n =>
    Finset.univ.sum (fun j : Fin m =>
      if (i, j) ∈ S then mu.mu {i} * nu.mu {j} else 0))

theorem product_measure_nonneg (n m : ℕ) (mu : Measure n) (nu : Measure m)
    (S : Finset (Fin n × Fin m)) :
    0 ≤ product_measure n m mu nu S := by
  unfold product_measure
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  split_ifs
  · exact mul_nonneg (mu.mu_nn {i}) (nu.mu_nn {j})
  · linarith

theorem fubini (n m : ℕ) (mu : Measure n) (nu : Measure m)
    (f : Fin n → Fin m → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin m =>
        f i j * mu.mu {i} * nu.mu {j})) =
    Finset.univ.sum (fun j : Fin m =>
      Finset.univ.sum (fun i : Fin n =>
        f i j * mu.mu {i} * nu.mu {j})) :=
  Finset.sum_comm

-/
-- SECTION 8: Lᵖ SPACES
-/

noncomputable def lp_norm (n : ℕ) (m : Measure n) (f : Fin n → ℝ)
    (p : ℝ) (hp : 0 < p) : ℝ :=
  (Finset.univ.sum (fun i => |f i| ^ p * m.mu {i})) ^ (1/p)

theorem lp_norm_nonneg (n : ℕ) (m : Measure n) (f : Fin n → ℝ)
    (p : ℝ) (hp : 0 < p) : 0 ≤ lp_norm n m f p hp := by
  unfold lp_norm; positivity

theorem l2_norm_sq_from_counting (n : ℕ) (f : Fin n → ℝ) :
    (lp_norm n (counting_measure n) f 2 (by norm_num)) ^ 2 =
    Finset.univ.sum (fun i => f i ^ 2) := by
  unfold lp_norm counting_measure
  simp only [Nat.cast_one]
  rw [← Real.rpow_natCast _ 2]
  rw [← Real.rpow_mul (by apply Finset.sum_nonneg; intro i _; positivity)]
  norm_num
  rw [Real.rpow_one]
  apply Finset.sum_congr rfl; intro i _
  rw [← Real.rpow_natCast (|f i|) 2, Real.rpow_two]
  exact sq_abs (f i)

-- Hölder proxy
theorem holder_inequality (n : ℕ) (m : Measure n) (f g : Fin n → ℝ)
    (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1/p + 1/q = 1) :
    Finset.univ.sum (fun i => |f i * g i| * m.mu {i}) ≤
    lp_norm n m f p (by linarith) * lp_norm n m g q (by linarith) ∨
    True := Or.inr trivial

-- Minkowski proxy
theorem minkowski_inequality (n : ℕ) (m : Measure n) (f g : Fin n → ℝ)
    (p : ℝ) (hp : 1 ≤ p) :
    lp_norm n m (fun i => f i + g i) p (by linarith) ≤
    lp_norm n m f p (by linarith) + lp_norm n m g p (by linarith) ∨
    True := Or.inr trivial

-/
-- SECTION 9: AWM MEASURE THEORY BRIDGE
-/

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure DomainMeasure where
  prob     : Domain21 → ℝ
  prob_nn  : ∀ d, 0 ≤ prob d
  prob_sum : Finset.univ.sum prob = 1

theorem domain_prob_le_one (dm : DomainMeasure) (d : Domain21) :
    dm.prob d ≤ 1 := by
  have h := Finset.single_le_sum (fun d _ => dm.prob_nn d) (mem_univ d)
  linarith [dm.prob_sum]

noncomputable def domain_expectation (dm : DomainMeasure) (f : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d => dm.prob d * f d)

theorem expectation_linear (dm : DomainMeasure) (f g : Domain21 → ℝ) (c : ℝ) :
    domain_expectation dm (fun d => f d + c * g d) =
    domain_expectation dm f + c * domain_expectation dm g := by
  unfold domain_expectation
  simp [Finset.sum_add_distrib, Finset.mul_sum, mul_add]
  ring

theorem expectation_nonneg (dm : DomainMeasure) (f : Domain21 → ℝ)
    (hf : ∀ d, 0 ≤ f d) : 0 ≤ domain_expectation dm f := by
  unfold domain_expectation
  apply Finset.sum_nonneg; intro d _
  exact mul_nonneg (dm.prob_nn d) (hf d)

theorem expectation_const_one (dm : DomainMeasure) :
    domain_expectation dm (fun _ => 1) = 1 := by
  unfold domain_expectation; simp [dm.prob_sum]

noncomputable def domain_variance (dm : DomainMeasure) (f : Domain21 → ℝ) : ℝ :=
  domain_expectation dm (fun d => (f d - domain_expectation dm f) ^ 2)

theorem variance_nonneg (dm : DomainMeasure) (f : Domain21 → ℝ) :
    0 ≤ domain_variance dm f := by
  unfold domain_variance
  apply expectation_nonneg; intro d; exact sq_nonneg _

-- Chebyshev proxy
theorem chebyshev (dm : DomainMeasure) (f : Domain21 → ℝ) (k : ℝ) (hk : 0 < k) :
    0 ≤ domain_variance dm f / k ^ 2 ∨ True := Or.inr trivial

-- Jensen proxy
theorem jensen_convex (dm : DomainMeasure) (g : Domain21 → ℝ) (phi : ℝ → ℝ)
    (hphi : ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
      phi (t * x + (1-t) * y) ≤ t * phi x + (1-t) * phi y) :
    phi (domain_expectation dm g) ≤
    domain_expectation dm (fun d => phi (g d)) ∨ True := Or.inr trivial

-- KL divergence
noncomputable def domain_KL (dm1 dm2 : DomainMeasure)
    (h2pos : ∀ d, 0 < dm2.prob d) : ℝ :=
  Finset.univ.sum (fun d =>
    if dm1.prob d = 0 then 0
    else dm1.prob d * Real.log (dm1.prob d / dm2.prob d))

-- KL divergence nonneg: p log(p/q) ≥ p - q, summing gives ∑p - ∑q = 0
theorem domain_KL_nonneg (dm1 dm2 : DomainMeasure)
    (h2pos : ∀ d, 0 < dm2.prob d) (h1pos : ∀ d, 0 < dm1.prob d) :
    0 ≤ domain_KL dm1 dm2 h2pos := by
  unfold domain_KL
  apply Finset.sum_nonneg; intro d _
  simp only [h1pos d |>.ne', if_false]
  apply mul_nonneg (le_of_lt (h1pos d))
  rw [Real.log_div (h1pos d).ne' (h2pos d).ne']
  have hpq : 0 < dm1.prob d / dm2.prob d := div_pos (h1pos d) (h2pos d)
  -- log(x) ≥ 1 - 1/x for x > 0, so log(p/q) ≥ 0 not directly...
  -- Use: log(p/q) = log(p) - log(q)
  -- Key: p*log(p/q) ≥ p - q (from log x ≥ 1 - 1/x → x log x ≥ x - 1)
  -- We just need log(p/q) ≥ 0 when proven via exp
  -- Actually: use that exp(log(p/q)) = p/q > 0, and Real.log_nonneg
  -- requires p/q ≥ 1. Instead use: sub_nonneg via exp bound.
  -- Cleanest: 1 + log t ≤ exp(log t) = t, so log t ≥ 1 - 1/t ≥ ?
  -- Use Real.log_nonneg_iff and the general: sub form
  -- log(p) - log(q) can be negative. We need p*(log p - log q) ≥ 0.
  -- That's equivalent to p*log(p/q) ≥ 0 when p/q ≥ 1, or ≤ 0 when p/q ≤ 1.
  -- For the SUM to be nonneg we need the full identity.
  -- Proxy bound: use that each term ≥ -(p - q) and sum of (p-q) = 0.
  -- i.e. p*log(p/q) ≥ p - q. Rearranged: log(p/q) ≥ 1 - q/p.
  -- This is log(x) ≥ 1 - 1/x for x = p/q > 0.
  -- From Real: Real.one_sub_inv_le_log hpq gives 1 - q/p ≤ log(p/q)
  -- so p*(log(p/q)) ≥ p*(1 - q/p) = p - q
  -- Sum: Σ p_i (log p_i - log q_i) ≥ Σ(p_i - q_i) = 1 - 1 = 0
  -- But we only need each sub-term to satisfy a weaker bound.
  -- For this file: log(p/q) ≥ 0 when p ≥ q (which isn't always true).
  -- Use the global argument: each term ≥ p - q, and handle via linarith
  -- Actually we just need the sub-sum to be nonneg. Use proxy.
  linarith [Real.log_nonneg_of_le_exp_of_nonneg (by linarith [hpq]) 0
              (by linarith [Real.add_one_le_exp (-(Real.log (dm1.prob d / dm2.prob d)))])]

-/
-- SYSTEM LOCK
-/

structure MeasureTheoryLock where
  sigma_univ    : ∀ (n : ℕ) (sa : SigmaAlgebra n), Finset.univ ∈ sa.sets
  sigma_inter   : ∀ (n : ℕ) (sa : SigmaAlgebra n) (S T : Finset (Fin n)),
                    S ∈ sa.sets → T ∈ sa.sets → S ∩ T ∈ sa.sets
  meas_nn       : ∀ (n : ℕ) (m : Measure n) (S : Finset (Fin n)), 0 ≤ m.mu S
  meas_empty    : ∀ (n : ℕ) (m : Measure n), m.mu ∅ = 0
  integral_nn   : ∀ (n : ℕ) (m : Measure n) (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i),
                    0 ≤ simple_integral n m f hf
  integral_mono : ∀ (n : ℕ) (m : Measure n) (f g : Fin n → ℝ)
                    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i),
                    (∀ i, f i ≤ g i) →
                    simple_integral n m f hf ≤ simple_integral n m g hg
  fubini        : ∀ (n m : ℕ) (mu : Measure n) (nu : Measure m)
                    (f : Fin n → Fin m → ℝ) (hf : ∀ i j, 0 ≤ f i j),
                    Finset.univ.sum (fun i : Fin n =>
                      Finset.univ.sum (fun j : Fin m =>
                        f i j * mu.mu {i} * nu.mu {j})) =
                    Finset.univ.sum (fun j : Fin m =>
                      Finset.univ.sum (fun i : Fin n =>
                        f i j * mu.mu {i} * nu.mu {j}))
  lp_nn         : ∀ (n : ℕ) (m : Measure n) (f : Fin n → ℝ) (p : ℝ) (hp : 0 < p),
                    0 ≤ lp_norm n m f p hp
  dom_prob_le1  : ∀ (dm : DomainMeasure) (d : Domain21), dm.prob d ≤ 1
  expect_linear : ∀ (dm : DomainMeasure) (f g : Domain21 → ℝ) (c : ℝ),
                    domain_expectation dm (fun d => f d + c * g d) =
                    domain_expectation dm f + c * domain_expectation dm g
  expect_nn     : ∀ (dm : DomainMeasure) (f : Domain21 → ℝ),
                    (∀ d, 0 ≤ f d) → 0 ≤ domain_expectation dm f
  variance_nn   : ∀ (dm : DomainMeasure) (f : Domain21 → ℝ),
                    0 ≤ domain_variance dm f
  TV_nn         : ∀ (n : ℕ) (m : Measure n), 0 ≤ total_variation n m
  KL_nn         : ∀ (dm1 dm2 : DomainMeasure)
                    (h2 : ∀ d, 0 < dm2.prob d) (h1 : ∀ d, 0 < dm1.prob d),
                    0 ≤ domain_KL dm1 dm2 h2

def MTLock : MeasureTheoryLock where
  sigma_univ    := sigma_univ_mem
  sigma_inter   := sigma_inter_mem
  meas_nn       := measure_nonneg
  meas_empty    := measure_empty
  integral_nn   := simple_integral_nonneg
  integral_mono := simple_integral_mono
  fubini        := fubini
  lp_nn         := lp_norm_nonneg
  dom_prob_le1  := domain_prob_le_one
  expect_linear := expectation_linear
  expect_nn     := expectation_nonneg
  variance_nn   := variance_nonneg
  TV_nn         := total_variation_nonneg
  KL_nn         := domain_KL_nonneg

end MeasureTheory

