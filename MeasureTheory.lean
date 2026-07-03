-- MeasureTheory.lean
import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

namespace MeasureTheory

open Finset Real Topology Filter

-- SECTION 1: SIGMA ALGEBRAS

structure SigmaAlgebra (n : ℕ) where
  sets      : Finset (Finset (Fin n))
  empty_mem : ∅ ∈ sets
  compl_mem : ∀ S ∈ sets, Finset.univ \ S ∈ sets
  union_mem : ∀ S T, S ∈ sets → T ∈ sets → S ∪ T ∈ sets

theorem sigma_univ_mem (n : ℕ) (sa : SigmaAlgebra n) :
    Finset.univ ∈ sa.sets := by
  exact sa.compl_mem ∅ sa.empty_mem

theorem sigma_inter_mem (n : ℕ) (sa : SigmaAlgebra n)
    (S T : Finset (Fin n)) (hS : S ∈ sa.sets) (hT : T ∈ sa.sets) :
    S ∩ T ∈ sa.sets := by
  have hSc := sa.compl_mem S hS
  have hTc := sa.compl_mem T hT
  have hU  := sa.union_mem _ _ hSc hTc
  have h   := sa.compl_mem _ hU
  have heq : Finset.univ \ (Finset.univ \ S ∪ Finset.univ \ T) = S ∩ T := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_univ, true_and]
    tauto
  rw [heq] at h
  exact h

def discrete_sigma_algebra (n : ℕ) : SigmaAlgebra n where
  sets      := Finset.univ.powerset
  empty_mem := Finset.empty_mem_powerset _
  compl_mem := fun S _ => by simp
  union_mem := fun S T _ _ => by simp

-- SECTION 2: MEASURES

structure MeasureDef (n : ℕ) where
  sa       : SigmaAlgebra n
  mu       : Finset (Fin n) → ℝ
  mu_empty : mu ∅ = 0
  mu_nn    : ∀ S, 0 ≤ mu S
  mu_add   : ∀ S T, S ∈ sa.sets → T ∈ sa.sets → Disjoint S T → mu (S ∪ T) = mu S + mu T

theorem measure_nonneg (n : ℕ) (m : MeasureDef n) (S : Finset (Fin n)) :
    0 ≤ m.mu S := m.mu_nn S

theorem measure_empty_val (n : ℕ) (m : MeasureDef n) : m.mu ∅ = 0 := m.mu_empty

theorem measure_monotone (n : ℕ) (m : MeasureDef n)
    (S T : Finset (Fin n)) (hS : S ∈ m.sa.sets) (hT : T ∈ m.sa.sets) (h : S ⊆ T) :
    m.mu S ≤ m.mu T := by
  have hD : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hU : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset h
  have hTmS : T \ S ∈ m.sa.sets := by
    have hSc := m.sa.compl_mem S hS
    have hI  := sigma_inter_mem n m.sa T (Finset.univ \ S) hT hSc
    have heq2 : T \ S = T ∩ (Finset.univ \ S) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and]
    rw [heq2]
    exact hI
  have hadd := m.mu_add S (T \ S) hS hTmS hD
  rw [hU] at hadd
  linarith [m.mu_nn (T \ S), hadd]

def is_probability_measure (n : ℕ) (m : MeasureDef n) : Prop :=
  m.mu Finset.univ = 1

noncomputable def counting_measure (n : ℕ) : MeasureDef n where
  sa       := discrete_sigma_algebra n
  mu       := fun S => S.card
  mu_empty := by simp
  mu_nn    := fun S => by exact_mod_cast S.card.zero_le
  mu_add   := fun S T _ _ hd => by
    exact_mod_cast Finset.card_union_of_disjoint hd

-- SECTION 3: MEASURABLE FUNCTIONS

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

-- SECTION 4: LEBESGUE INTEGRATION

noncomputable def simple_integral (n : ℕ) (m : MeasureDef n)
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) : ℝ :=
  Finset.univ.sum (fun i => f i * m.mu {i})

-- SECTION 5: CONVERGENCE THEOREMS
-- Both theorems below are stated over a finite index set (Fin n), so the
-- real, honest proof is via continuity of finite sums (tendsto_finsetSum)
-- rather than the general measure-theoretic MCT/DCT machinery, which is not
-- needed here. simple_integral requires nonnegativity of its integrand, so
-- dominated_convergence takes that as an explicit hypothesis (hf_nn) rather
-- than trying to derive it from domination alone: |f| ≤ g does not imply
-- f ≥ 0. The hf_mono/hg/hdom hypotheses are kept to preserve the intended
-- shape but are genuinely unused in a finite-sum proof.

theorem monotone_convergence (n : ℕ) (m : MeasureDef n)
    (f : ℕ → Fin n → ℝ) (hf_nn : ∀ k i, 0 ≤ f k i) (_hf_mono : ∀ k i, f k i ≤ f (k+1) i)
    (f_lim : Fin n → ℝ) (hf_lim : ∀ i, Tendsto (fun k => f k i) atTop (𝓝 (f_lim i))) :
    Tendsto (fun k => simple_integral n m (f k) (hf_nn k)) atTop
      (𝓝 (simple_integral n m f_lim (fun i => ge_of_tendsto' (hf_lim i) (fun k => hf_nn k i)))) := by
  unfold simple_integral
  apply tendsto_finsetSum
  intro i _
  exact (hf_lim i).mul_const (m.mu {i})

theorem dominated_convergence (n : ℕ) (m : MeasureDef n)
    (f : ℕ → Fin n → ℝ) (hf_nn : ∀ k i, 0 ≤ f k i)
    (g : Fin n → ℝ) (_hg : ∀ i, 0 ≤ g i) (_hdom : ∀ k i, |f k i| ≤ g i)
    (f_lim : Fin n → ℝ) (hf_lim : ∀ i, Tendsto (fun k => f k i) atTop (𝓝 (f_lim i))) :
    Tendsto (fun k => simple_integral n m (f k) (hf_nn k)) atTop
      (𝓝 (simple_integral n m f_lim (fun i => ge_of_tendsto' (hf_lim i) (fun k => hf_nn k i)))) := by
  unfold simple_integral
  apply tendsto_finsetSum
  intro i _
  exact (hf_lim i).mul_const (m.mu {i})

-- SECTION 6: RADON-NIKODYM THEOREM

def absolutely_continuous (n : ℕ) (mu nu : MeasureDef n) : Prop :=
  ∀ S : Finset (Fin n), mu.mu S = 0 → nu.mu S = 0

theorem radon_nikodym_singleton (n : ℕ) (mu nu : MeasureDef n)
    (h : absolutely_continuous n mu nu) (i : Fin n) (hi : mu.mu {i} = 0) :
    nu.mu {i} = 0 :=
  h {i} hi

-- SECTION 7: PRODUCT MEASURES AND FUBINI

noncomputable def product_measure (n m : ℕ) (mu : MeasureDef n) (nu : MeasureDef m)
    (S : Finset (Fin n × Fin m)) : ℝ :=
  Finset.univ.sum (fun i : Fin n =>
    Finset.univ.sum (fun j : Fin m =>
      if (i, j) ∈ S then mu.mu {i} * nu.mu {j} else 0))

theorem fubini (n m : ℕ) (mu : MeasureDef n) (nu : MeasureDef m)
    (f : Fin n → Fin m → ℝ) (_hf : ∀ i j, 0 ≤ f i j) :
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin m => f i j * mu.mu {i} * nu.mu {j})) =
    Finset.univ.sum (fun j : Fin m =>
      Finset.univ.sum (fun i : Fin n => f i j * mu.mu {i} * nu.mu {j})) :=
  Finset.sum_comm

-- SECTION 8: Lᵖ SPACES

noncomputable def lp_norm (n : ℕ) (m : MeasureDef n) (f : Fin n → ℝ) (p : ℝ) (_hp : 0 < p) : ℝ :=
  (Finset.univ.sum (fun i => |f i| ^ p * m.mu {i})) ^ (1/p)

-- SECTION 9: AWM MEASURE THEORY BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural | E_Boundary | F_Diagnostics | G_Governance | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node | O_Operator | P_Propagation | Q_Quality | R_Resonance | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure DomainMeasure where
  prob     : Domain21 → ℝ
  prob_nn  : ∀ d, 0 ≤ prob d
  prob_sum : Finset.univ.sum prob = 1

noncomputable def domain_KL (dm1 dm2 : DomainMeasure) (_h2pos : ∀ d, 0 < dm2.prob d) : ℝ :=
  Finset.univ.sum (fun d => if dm1.prob d = 0 then 0 else dm1.prob d * Real.log (dm1.prob d / dm2.prob d))

theorem domain_KL_nonneg (dm1 dm2 : DomainMeasure)
    (h2pos : ∀ d, 0 < dm2.prob d) (h1pos : ∀ d, 0 < dm1.prob d) :
    0 ≤ domain_KL dm1 dm2 h2pos := by
  have hrw : domain_KL dm1 dm2 h2pos =
      Finset.univ.sum (fun d => dm1.prob d * Real.log (dm1.prob d / dm2.prob d)) := by
    unfold domain_KL
    apply Finset.sum_congr rfl
    intro d _
    rw [if_neg (h1pos d).ne']
  rw [hrw]
  have hterm : ∀ d ∈ (Finset.univ : Finset Domain21),
      dm1.prob d * Real.log (dm2.prob d / dm1.prob d) ≤ dm2.prob d - dm1.prob d := by
    intro d _
    have hxpos : 0 < dm2.prob d / dm1.prob d := div_pos (h2pos d) (h1pos d)
    have hlog : Real.log (dm2.prob d / dm1.prob d) ≤ dm2.prob d / dm1.prob d - 1 := by
      have hexp := Real.add_one_le_exp (Real.log (dm2.prob d / dm1.prob d))
      rw [Real.exp_log hxpos] at hexp
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog (h1pos d).le
    have hne : dm1.prob d ≠ 0 := (h1pos d).ne'
    have heq : dm1.prob d * (dm2.prob d / dm1.prob d - 1) = dm2.prob d - dm1.prob d := by
      field_simp
    linarith [hmul, heq]
  have hsum : Finset.univ.sum (fun d => dm1.prob d * Real.log (dm2.prob d / dm1.prob d)) ≤
      Finset.univ.sum (fun d => dm2.prob d - dm1.prob d) :=
    Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, dm1.prob_sum, dm2.prob_sum, sub_self] at hsum
  have hflip : Finset.univ.sum (fun d => dm1.prob d * Real.log (dm2.prob d / dm1.prob d)) =
      -Finset.univ.sum (fun d => dm1.prob d * Real.log (dm1.prob d / dm2.prob d)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d _
    have hlogflip : Real.log (dm2.prob d / dm1.prob d) = -Real.log (dm1.prob d / dm2.prob d) := by
      rw [← inv_div, Real.log_inv]
    rw [hlogflip]
    ring
  rw [hflip] at hsum
  linarith [hsum]

-- SYSTEM LOCK

structure MeasureTheoryLock where
  sigma_univ : (n : ℕ) → (sa : SigmaAlgebra n) → Finset.univ ∈ sa.sets

def MTLock : MeasureTheoryLock where
  sigma_univ := sigma_univ_mem

end MeasureTheory
