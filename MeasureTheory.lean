import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
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
  rw [compl_union] at h
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
    rw [sdiff_eq_inter] at hI
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

theorem monotone_convergence (n : ℕ) (m : MeasureDef n)
    (f : ℕ → Fin n → ℝ) (hf_nn : ∀ k i, 0 ≤ f k i) (hf_mono : ∀ k i, f k i ≤ f (k+1) i)
    (f_lim : Fin n → ℝ) (hf_lim : ∀ i, Tendsto (fun k => f k i) atTop (𝓝 (f_lim i))) :
    Tendsto (fun k => simple_integral n m (f k) (hf_nn k)) atTop (𝓝 (simple_integral n m f_lim (fun i => le_of_tendsto (hf_lim i) (Filter.univ_mem)))) := by
  sorry

theorem dominated_convergence (n : ℕ) (m : MeasureDef n)
    (f : ℕ → Fin n → ℝ) (g : Fin n → ℝ) (hg : ∀ i, 0 ≤ g i) (hdom : ∀ k i, |f k i| ≤ g i)
    (f_lim : Fin n → ℝ) (hf_lim : ∀ i, Tendsto (fun k => f k i) atTop (𝓝 (f_lim i))) :
    Tendsto (fun k => simple_integral n m (f k) (fun i => le_trans (abs_nonneg _) (hdom k i))) atTop (𝓝 (simple_integral n m f_lim (fun i => le_of_tendsto (hf_lim i) (Filter.univ_mem)))) := by
  sorry

-- SECTION 6: RADON-NIKODYM THEOREM

def absolutely_continuous (n : ℕ) (mu nu : MeasureDef n) : Prop :=
  ∀ S : Finset (Fin n), mu.mu S = 0 → nu.mu S = 0

theorem radon_nikodym (n : ℕ) (mu nu : MeasureDef n) (h : absolutely_continuous n mu nu) :
    ∃ f : Fin n → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ S, nu.mu S = simple_integral n mu (fun i => if i ∈ S then f i else 0) (fun i => by split_ifs <;> linarith [f_nonneg i])) :=
    ⟨fun i => nu.mu {i} / (mu.mu {i} + 1), fun i => div_nonneg (nu.mu_nn _) (add_nonneg (mu.mu_nn _) zero_le_one), sorry⟩
    where f_nonneg i := div_nonneg (nu.mu_nn _) (add_nonneg (mu.mu_nn _) zero_le_one)

-- SECTION 7: PRODUCT MEASURES AND FUBINI

noncomputable def product_measure (n m : ℕ) (mu : MeasureDef n) (nu : MeasureDef m)
    (S : Finset (Fin n × Fin m)) : ℝ :=
  Finset.univ.sum (fun i : Fin n =>
    Finset.univ.sum (fun j : Fin m =>
      if (i, j) ∈ S then mu.mu {i} * nu.mu {j} else 0))

theorem fubini (n m : ℕ) (mu : MeasureDef n) (nu : MeasureDef m)
    (f : Fin n → Fin m → ℝ) (hf : ∀ i j, 0 ≤ f i j) :
    Finset.univ.sum (fun i : Fin n =>
      Finset.univ.sum (fun j : Fin m => f i j * mu.mu {i} * nu.mu {j})) =
    Finset.univ.sum (fun j : Fin m =>
      Finset.univ.sum (fun i : Fin n => f i j * mu.mu {i} * nu.mu {j})) :=
  Finset.sum_comm

-- SECTION 8: Lᵖ SPACES

noncomputable def lp_norm (n : ℕ) (m : MeasureDef n) (f : Fin n → ℝ) (p : ℝ) (hp : 0 < p) : ℝ :=
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

noncomputable def domain_KL (dm1 dm2 : DomainMeasure) (h2pos : ∀ d, 0 < dm2.prob d) : ℝ :=
  Finset.univ.sum (fun d => if dm1.prob d = 0 then 0 else dm1.prob d * Real.log (dm1.prob d / dm2.prob d))

theorem domain_KL_nonneg (dm1 dm2 : DomainMeasure) (h2pos : ∀ d, 0 < dm2.prob d) (h1pos : ∀ d, 0 < dm1.prob d) :
    0 ≤ domain_KL dm1 dm2 h2pos := by
  unfold domain_KL
  apply Finset.sum_nonneg
  intro d _
  by_cases h : dm1.prob d = 0
  · simp [h]
  · apply mul_nonneg (le_of_lt (h1pos d))
    apply log_nonneg
    apply le_of_one_le
    apply le_div_self (h1pos d) (h2pos d)
    sorry

-- SYSTEM LOCK

structure MeasureTheoryLock where
  sigma_univ : (n : ℕ) → (sa : SigmaAlgebra n) → Finset.univ ∈ sa.sets

def MTLock : MeasureTheoryLock where
  sigma_univ := sigma_univ_mem

end MeasureTheory

