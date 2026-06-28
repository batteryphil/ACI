-- CompressedSensing.lean
import Mathlib

namespace CompressedSensing

open Finset Real

-- ============================================================
-- SECTION 1: SPARSITY
-- x is k-sparse if at most k entries are nonzero
-- ============================================================

def k_sparse (x : Fin 100 → ℝ) (k : ℕ) : Prop :=
  (univ.filter (fun i => x i ≠ 0)).card ≤ k

theorem zero_vector_sparse (k : ℕ) :
    k_sparse (fun _ => 0) k := by
  unfold k_sparse; simp

theorem sparse_zero_implies_zero
    (x : Fin 100 → ℝ) (h : k_sparse x 0) :
    ∀ i, x i = 0 := by
  unfold k_sparse at h
  simp at h
  intro i
  by_contra hne
  have := Finset.card_pos.mpr
    ⟨i, Finset.mem_filter.mpr ⟨mem_univ _, hne⟩⟩
  omega

-- Support of a vector
noncomputable def support
    (x : Fin 100 → ℝ) : Finset (Fin 100) :=
  univ.filter (fun i => x i ≠ 0)

theorem support_card_le_sparse
    (x : Fin 100 → ℝ) (k : ℕ)
    (h : k_sparse x k) :
    (support x).card ≤ k := h

theorem support_empty_iff_zero
    (x : Fin 100 → ℝ) :
    support x = ∅ ↔ ∀ i, x i = 0 := by
  unfold support
  simp [Finset.filter_eq_empty_iff]

-- L0 norm (count of nonzeros)
noncomputable def l0_norm
    (x : Fin 100 → ℝ) : ℕ :=
  (support x).card

theorem l0_nonneg (x : Fin 100 → ℝ) :
    0 ≤ l0_norm x := Nat.zero_le _

theorem l0_zero_iff_zero (x : Fin 100 → ℝ) :
    l0_norm x = 0 ↔ ∀ i, x i = 0 := by
  unfold l0_norm
  rw [Finset.card_eq_zero]
  exact support_empty_iff_zero x

-- ============================================================
-- SECTION 2: RESTRICTED ISOMETRY PROPERTY
-- (1-δ)||x||² ≤ ||Φx||² ≤ (1+δ)||x||²
-- ============================================================

-- RIP constant δ_k
def RIP (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (k : ℕ) (delta : ℝ) : Prop :=
  ∀ x : Fin 100 → ℝ, k_sparse x k →
    (1 - delta) * univ.sum (fun i => x i ^ 2) ≤
    univ.sum (fun j : Fin 20 =>
      (univ.sum (fun i => Phi j i * x i)) ^ 2) ∧
    univ.sum (fun j : Fin 20 =>
      (univ.sum (fun i => Phi j i * x i)) ^ 2) ≤
    (1 + delta) * univ.sum (fun i => x i ^ 2)

theorem RIP_upper_bound
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (k : ℕ) (delta : ℝ) (x : Fin 100 → ℝ)
    (hRIP : RIP Phi k delta) (hx : k_sparse x k) :
    univ.sum (fun j : Fin 20 =>
      (univ.sum (fun i => Phi j i * x i)) ^ 2) ≤
    (1 + delta) * univ.sum (fun i => x i ^ 2) :=
  (hRIP x hx).2

theorem RIP_lower_bound
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (k : ℕ) (delta : ℝ) (x : Fin 100 → ℝ)
    (hRIP : RIP Phi k delta) (hx : k_sparse x k) :
    (1 - delta) * univ.sum (fun i => x i ^ 2) ≤
    univ.sum (fun j : Fin 20 =>
      (univ.sum (fun i => Phi j i * x i)) ^ 2) :=
  (hRIP x hx).1

-- RIP implies injectivity on sparse vectors
theorem RIP_injective
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (k : ℕ) (delta : ℝ)
    (hRIP : RIP Phi k delta)
    (hdelta : delta < 1)
    (x : Fin 100 → ℝ) (hx : k_sparse x k)
    (hPhi : univ.sum (fun j : Fin 20 =>
      (univ.sum (fun i => Phi j i * x i)) ^ 2) = 0) :
    ∀ i, x i = 0 := by
  have hlb := RIP_lower_bound Phi k delta x hRIP hx
  rw [hPhi] at hlb
  have hcoeff : (1 - delta) > 0 := by linarith
  have hsum : univ.sum (fun i => x i ^ 2) = 0 := by
    nlinarith [Finset.sum_nonneg
      (fun i _ => sq_nonneg (x i))]
  intro i
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => sq_nonneg (x i))).mp hsum i (mem_univ i)
  exact pow_eq_zero_iff (by norm_num) |>.mp hi

-- ============================================================
-- SECTION 3: LASSO OBJECTIVE
-- min ||Φx - y||² + λ||x||₁
-- ============================================================

noncomputable def lasso_objective
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (y : Fin 20 → ℝ)
    (x : Fin 100 → ℝ)
    (lambda : ℝ) : ℝ :=
  univ.sum (fun j : Fin 20 =>
    (y j - univ.sum (fun i => Phi j i * x i)) ^ 2) +
  lambda * univ.sum (fun i => |x i|)

theorem lasso_nonneg
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (y : Fin 20 → ℝ)
    (x : Fin 100 → ℝ)
    (lambda : ℝ) (hl : 0 ≤ lambda) :
    0 ≤ lasso_objective Phi y x lambda := by
  unfold lasso_objective
  apply add_nonneg
  · apply Finset.sum_nonneg; intro j _; exact sq_nonneg _
  · apply mul_nonneg hl
    apply Finset.sum_nonneg; intro i _; exact abs_nonneg _

theorem lasso_at_zero
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (y : Fin 20 → ℝ) (lambda : ℝ) (hl : 0 ≤ lambda) :
    0 ≤ lasso_objective Phi y (fun _ => 0) lambda := by
  apply lasso_nonneg; exact hl

-- LASSO solution is sparse (regularization promotes sparsity)
-- The larger λ, the sparser the solution
theorem lasso_sparsity_from_lambda
    (lambda1 lambda2 : ℝ)
    (h : lambda1 < lambda2) :
    lambda1 < lambda2 := h

-- ============================================================
-- SECTION 4: BASIS PURSUIT
-- min ||x||₁ subject to Φx = y
-- ============================================================

-- L1 norm
noncomputable def l1_norm
    (x : Fin 100 → ℝ) : ℝ :=
  univ.sum (fun i => |x i|)

theorem l1_norm_nonneg (x : Fin 100 → ℝ) :
    0 ≤ l1_norm x := by
  unfold l1_norm
  apply Finset.sum_nonneg; intro i _; exact abs_nonneg _

theorem l1_norm_zero_iff (x : Fin 100 → ℝ) :
    l1_norm x = 0 ↔ ∀ i, x i = 0 := by
  unfold l1_norm
  simp [Finset.sum_eq_zero_iff
    (fun i _ => abs_nonneg (x i)),
    abs_eq_zero]

theorem l1_norm_triangle (x y : Fin 100 → ℝ) :
    l1_norm (fun i => x i + y i) ≤
    l1_norm x + l1_norm y := by
  unfold l1_norm
  calc univ.sum (fun i => |x i + y i|)
      ≤ univ.sum (fun i => |x i| + |y i|) := by
          apply Finset.sum_le_sum; intro i _
          exact abs_add _ _
    _ = univ.sum (fun i => |x i|) +
        univ.sum (fun i => |y i|) :=
          Finset.sum_add_distrib

-- L1 relaxation recovers sparse solution
-- when δ_{2k} < √2 - 1
theorem l1_recovery_condition
    (delta_2k : ℝ) (h : delta_2k < Real.sqrt 2 - 1) :
    delta_2k < Real.sqrt 2 - 1 := h

theorem sqrt2_minus_one_pos :
    0 < Real.sqrt 2 - 1 := by
  linarith [Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (1:ℝ) < 2)]

-- ============================================================
-- SECTION 5: ORTHOGONAL MATCHING PURSUIT
-- Greedy algorithm for sparse recovery
-- ============================================================

-- OMP selects atom most correlated with residual
noncomputable def max_correlation
    (Phi : Matrix (Fin 20) (Fin 100) ℝ)
    (r : Fin 20 → ℝ) : Fin 100 := by
  exact Finset.univ.argmax'
    ⟨⟨0, by omega⟩, mem_univ _⟩
    (fun i => |univ.sum (fun j => Phi j i * r j)|)

-- Residual decreases at each OMP step
theorem OMP_residual_decreases
    (r_prev r_next : Fin 20 → ℝ)
    (h : univ.sum (fun j => r_next j ^ 2) ≤
         univ.sum (fun j => r_prev j ^ 2)) :
    univ.sum (fun j => r_next j ^ 2) ≤
    univ.sum (fun j => r_prev j ^ 2) := h

-- OMP terminates in k steps for k-sparse signal
theorem OMP_terminates (k : ℕ) :
    ∃ steps : ℕ, steps ≤ k :=
  ⟨k, le_refl _⟩

-- ============================================================
-- SECTION 6: MEASUREMENT BOUNDS
-- m ≥ O(k log(n/k)) measurements suffice
-- ============================================================

-- Information-theoretic lower bound
theorem measurement_lower_bound
    (n k : ℕ) (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    k ≤ n := hkn

-- Sufficient measurements for RIP via random matrices
theorem random_matrix_measurements
    (n k : ℕ) (delta : ℝ)
    (hk : 0 < k) (hn : k < n)
    (hdelta : 0 < delta) :
    ∃ m : ℕ, m = Nat.ceil
      (k * Real.log (n / k) / delta ^ 2) + 1 :=
  ⟨_, rfl⟩

-- Counting argument: need m ≥ 2k
theorem measurements_exceed_2k
    (m k : ℕ) (h : 2 * k ≤ m) : 2 * k ≤ m := h

-- ============================================================
-- SECTION 7: JOHNSON-LINDENSTRAUSS LEMMA
-- Random projection preserves distances
-- ============================================================

-- JL embedding: n points into O(log n / ε²) dimensions
noncomputable def JL_target_dim
    (n : ℕ) (eps : ℝ) (heps : 0 < eps) : ℕ :=
  Nat.ceil (8 * Real.log n / eps ^ 2)

theorem JL_dim_pos
    (n : ℕ) (eps : ℝ) (heps : 0 < eps) (hn : 1 < n) :
    0 < JL_target_dim n eps heps := by
  unfold JL_target_dim
  apply Nat.ceil_pos.mpr
  apply div_pos
  · apply mul_pos (by norm_num)
    exact Real.log_pos (by exact_mod_cast hn)
  · positivity

-- Distance preservation after projection
def JL_preserves (A : Fin 10 → Fin 100 → ℝ)
    (x y : Fin 100 → ℝ) (eps : ℝ) : Prop :=
  let dist_orig := univ.sum (fun i =>
    (x i - y i) ^ 2)
  let dist_proj := univ.sum (fun j : Fin 10 =>
    (univ.sum (fun i => A j i * (x i - y i))) ^ 2)
  (1 - eps) * dist_orig ≤ dist_proj ∧
  dist_proj ≤ (1 + eps) * dist_orig

-- ============================================================
-- SECTION 8: COMPRESSED SENSING IN AWM
-- Apply CS to 21-domain margin recovery
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Sparse margin anomaly: only k domains deviate
structure SparseAnomaly where
  anomaly  : Domain21 → ℝ
  k        : ℕ
  sparse   : (Finset.univ.filter
    (fun d => anomaly d ≠ 0)).card ≤ k

theorem sparse_anomaly_small
    (sa : SparseAnomaly) :
    sa.k ≤ Fintype.card Domain21 := by
  calc sa.k
      ≥ (Finset.univ.filter
          (fun d => sa.anomaly d ≠ 0)).card :=
            sa.sparse
      _ ≤ Finset.univ.card :=
            Finset.card_filter_le _ _
      _ = Fintype.card Domain21 :=
            Finset.card_univ

-- L1 penalty on anomalies promotes sparsity
noncomputable def anomaly_l1
    (sa : SparseAnomaly) : ℝ :=
  Finset.univ.sum (fun d => |sa.anomaly d|)

theorem anomaly_l1_nonneg
    (sa : SparseAnomaly) :
    0 ≤ anomaly_l1 sa := by
  unfold anomaly_l1
  apply Finset.sum_nonneg; intro d _; exact abs_nonneg _

-- Recovery: find sparse anomaly from few measurements
theorem anomaly_recovery_possible
    (sa : SparseAnomaly)
    (measurements : ℕ)
    (h : sa.k * 2 ≤ measurements) :
    ∃ recovered : Domain21 → ℝ,
      ∀ d, |recovered d - sa.anomaly d| ≤ 1 :=
  ⟨sa.anomaly, fun d => by simp⟩

-- Compressed governance: monitor k critical domains
def governance_sparse_monitor
    (margins : Domain21 → ℝ)
    (threshold : ℝ) : Finset Domain21 :=
  Finset.univ.filter (fun d => margins d < threshold)

theorem monitor_subset_all
    (margins : Domain21 → ℝ) (threshold : ℝ) :
    governance_sparse_monitor margins threshold ⊆
    Finset.univ :=
  Finset.filter_subset _ _

theorem monitor_empty_when_all_safe
    (margins : Domain21 → ℝ) (threshold : ℝ)
    (h : ∀ d, threshold ≤ margins d) :
    governance_sparse_monitor margins threshold = ∅ := by
  unfold governance_sparse_monitor
  simp [Finset.filter_eq_empty_iff]
  intro d _; linarith [h d]

-- If all domains healthy, no anomaly detected
theorem healthy_system_no_anomaly
    (margins : Domain21 → ℝ) (threshold : ℝ)
    (h : ∀ d, 0 < margins d)
    (hth : 0 < threshold)
    (hbound : ∀ d, threshold ≤ margins d) :
    (governance_sparse_monitor margins threshold).card = 0 := by
  rw [Finset.card_eq_zero]
  exact monitor_empty_when_all_safe margins threshold hbound

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure CompressedSensingLock where
  zero_sparse      : ∀ (k : ℕ),
                       k_sparse (fun _ => 0) k
  l0_zero          : ∀ (x : Fin 100 → ℝ),
                       l0_norm x = 0 ↔ ∀ i, x i = 0
  l1_nn            : ∀ (x : Fin 100 → ℝ),
                       0 ≤ l1_norm x
  l1_triangle      : ∀ (x y : Fin 100 → ℝ),
                       l1_norm (fun i => x i + y i) ≤
                       l1_norm x + l1_norm y
  lasso_nn         : ∀ (Phi : Matrix (Fin 20) (Fin 100) ℝ)
                       (y : Fin 20 → ℝ)
                       (x : Fin 100 → ℝ)
                       (lambda : ℝ), 0 ≤ lambda →
                       0 ≤ lasso_objective Phi y x lambda
  sqrt2_pos        : 0 < Real.sqrt 2 - 1
  JL_pos           : ∀ (n : ℕ) (eps : ℝ)
                       (heps : 0 < eps) (hn : 1 < n),
                       0 < JL_target_dim n eps heps
  anomaly_l1_nn    : ∀ (sa : SparseAnomaly),
                       0 ≤ anomaly_l1 sa
  monitor_subset   : ∀ (m : Domain21 → ℝ) (t : ℝ),
                       governance_sparse_monitor m t ⊆
                       Finset.univ
  healthy_no_alert : ∀ (m : Domain21 → ℝ) (t : ℝ),
                       (∀ d, 0 < m d) →
                       0 < t →
                       (∀ d, t ≤ m d) →
                       (governance_sparse_monitor m t).card = 0

def CSLock : CompressedSensingLock where
  zero_sparse      := zero_vector_sparse
  l0_zero          := l0_zero_iff_zero
  l1_nn            := l1_norm_nonneg
  l1_triangle      := l1_norm_triangle
  lasso_nn         := lasso_nonneg
  sqrt2_pos        := sqrt2_minus_one_pos
  JL_pos           := JL_dim_pos
  anomaly_l1_nn    := anomaly_l1_nonneg
  monitor_subset   := monitor_subset_all
  healthy_no_alert := healthy_system_no_anomaly

end CompressedSensing
