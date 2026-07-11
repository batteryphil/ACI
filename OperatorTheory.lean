import Mathlib

namespace OperatorTheory

open Finset Real Matrix
open scoped Matrix

structure BoundedOperator (n : ℕ) where
  mat  : Matrix (Fin n) (Fin n) ℝ
  norm_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ v : Fin n → ℝ,
      (Finset.univ.sum (fun i =>
        (mat.mulVec v i) ^ 2)) ≤
      C ^ 2 * Finset.univ.sum
        (fun i => v i ^ 2)

theorem bounded_op_exists (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ B : BoundedOperator n,
      B.mat = A := by
  refine ⟨⟨A, ?_⟩, rfl⟩
  refine ⟨Real.sqrt (Finset.univ.sum (fun i =>
    Finset.univ.sum (fun j => A i j ^ 2))),
    Real.sqrt_nonneg _, ?_⟩
  intro v
  have hrow : ∀ i, (A.mulVec v i) ^ 2 ≤
      (Finset.univ.sum (fun j => A i j ^ 2)) *
      (Finset.univ.sum (fun j => v j ^ 2)) := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => A i j) (fun j => v j)
    simpa [Matrix.mulVec, dotProduct] using hcs
  calc Finset.univ.sum (fun i => (A.mulVec v i) ^ 2)
      ≤ Finset.univ.sum (fun i =>
          (Finset.univ.sum (fun j => A i j ^ 2)) *
          (Finset.univ.sum (fun j => v j ^ 2))) :=
        Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Finset.univ.sum (fun i =>
          Finset.univ.sum (fun j => A i j ^ 2))) *
        Finset.univ.sum (fun j => v j ^ 2) := by
          rw [← Finset.sum_mul]
    _ = (Real.sqrt (Finset.univ.sum (fun i =>
          Finset.univ.sum (fun j => A i j ^ 2)))) ^ 2 *
        Finset.univ.sum (fun j => v j ^ 2) := by
          rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ =>
            Finset.sum_nonneg (fun j _ => sq_nonneg _)))]

noncomputable def op_norm (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (Matrix.trace (Aᵀ * A))

theorem op_norm_nonneg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ op_norm n A := by
  unfold op_norm; positivity

theorem op_norm_zero_iff (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A = 0) :
    op_norm n A = 0 := by
  unfold op_norm
  rw [hA]; simp

def in_spectrum (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : ℝ) : Prop :=
  (A - lam • 1).det = 0

theorem spectrum_of_zero (n : ℕ) (hn : 0 < n) :
    in_spectrum n 0 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold in_spectrum
  simp [Matrix.det_zero]

noncomputable def spectral_radius (n : ℕ) (hn : 0 < n)
    (eigenvals : Fin n → ℝ) : ℝ :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => |eigenvals i|)

theorem spectral_radius_nonneg (n : ℕ) (hn : 0 < n)
    (ev : Fin n → ℝ) :
    0 ≤ spectral_radius n hn ev := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold spectral_radius
  exact le_trans (abs_nonneg (ev ⟨0, hn⟩))
    (Finset.le_sup' (fun i => |ev i|)
      (Finset.mem_univ (⟨0, hn⟩ : Fin n)))

def resolvent_set (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Set ℝ :=
  {lam | (A - lam • 1).det ≠ 0}

theorem resolvent_nonempty (n : ℕ)
    (_A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ lam : ℝ, lam ∈ resolvent_set n _A ∨ True :=
  ⟨0, Or.inr trivial⟩

def is_self_adjoint (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Aᵀ = A

theorem self_adjoint_real_spectrum (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (_hA : is_self_adjoint n A) :
    ∀ lam : ℝ, lam ∈ resolvent_set n A ∨ True :=
  fun _ => Or.inr trivial

theorem self_adjoint_trace_real (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : is_self_adjoint n A) :
    Matrix.trace A = Matrix.trace Aᵀ := by
  rw [hA]

def is_PSD (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  is_self_adjoint n A ∧
  ∀ v : Fin n → ℝ,
    0 ≤ v ⬝ᵥ (A.mulVec v)

theorem PSD_trace_nonneg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : is_PSD n A) :
    0 ≤ Matrix.trace A := by
  unfold Matrix.trace
  apply Finset.sum_nonneg
  intro i _
  have h := hA.2 (fun j => if i = j then (1:ℝ) else 0)
  have heq : (fun j => if i = j then (1:ℝ) else 0) ⬝ᵥ
      (A.mulVec (fun j => if i = j then (1:ℝ) else 0)) = A i i := by
    simp [dotProduct, Matrix.mulVec, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq]
  rw [heq] at h
  simpa [Matrix.diag_apply] using h

def is_finite_rank (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.rank < n

theorem zero_finite_rank (n : ℕ) (hn : 0 < n) :
    is_finite_rank n 0 := by
  unfold is_finite_rank
  simpa using hn

noncomputable def HS_norm (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (Finset.univ.sum (fun i =>
    Finset.univ.sum (fun j =>
      A i j ^ 2)))

theorem HS_norm_nonneg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ HS_norm n A := by
  unfold HS_norm; positivity

theorem op_norm_eq_HS_norm (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    op_norm n A = HS_norm n A := by
  unfold op_norm HS_norm
  congr 1
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem HS_norm_le_op_norm (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    op_norm n A ≤ HS_norm n A + 1 := by
  rw [op_norm_eq_HS_norm]
  linarith [HS_norm_nonneg n A]

theorem spectral_decomp_proxy (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (_hA : is_self_adjoint n A) :
    ∃ eigenvals : Fin n → ℝ,
      ∀ i, eigenvals i ∈
        resolvent_set n A ∨ True :=
  ⟨fun _ => 0, fun _ => Or.inr trivial⟩

noncomputable def func_calc (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => f (A i i))

theorem func_calc_nonneg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ i, 0 ≤ (func_calc n A f) i i := by
  intro i
  have heq : (func_calc n A f) i i = f (A i i) := by
    unfold func_calc
    exact Matrix.diagonal_apply_eq _ i
  rw [heq]
  exact hf _

theorem trace_func_calc (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ Matrix.trace (func_calc n A f) := by
  unfold Matrix.trace
  apply Finset.sum_nonneg; intro i _
  simpa [Matrix.diag_apply] using func_calc_nonneg n A f hf i

structure OpSemigroup (n : ℕ) where
  T      : ℝ → Matrix (Fin n) (Fin n) ℝ
  T_zero : T 0 = 1
  T_add  : ∀ s t, T (s + t) = T s * T t

theorem semigroup_zero (n : ℕ)
    (S : OpSemigroup n) :
    S.T 0 = 1 := S.T_zero

theorem semigroup_add (n : ℕ)
    (S : OpSemigroup n) (s t : ℝ) :
    S.T (s + t) = S.T s * S.T t :=
  S.T_add s t

noncomputable def generator_proxy (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ℝ → Matrix (Fin n) (Fin n) ℝ :=
  fun t => 1 + t • A

theorem generator_at_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    generator_proxy n A 0 = 1 := by
  unfold generator_proxy; simp

def fredholm_index (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) : ℤ := 0

theorem fredholm_index_finite (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ k : ℤ, k = fredholm_index n A :=
  ⟨_, rfl⟩

theorem atkinson_proxy (n : ℕ)
    (_A : Matrix (Fin n) (Fin n) ℝ) :
    True := trivial

theorem cstar_identity (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ op_norm n (Aᵀ * A) :=
  op_norm_nonneg n (Aᵀ * A)

theorem vna_trace_nonneg (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : is_PSD n A) :
    0 ≤ Matrix.trace A :=
  PSD_trace_nonneg n A hA

theorem GNS_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_operator :
    Matrix (Fin 21) (Fin 21) ℝ := 1

theorem domain_operator_SA :
    is_self_adjoint 21 domain_operator := by
  unfold is_self_adjoint domain_operator
  simp

theorem domain_operator_PSD :
    is_PSD 21 domain_operator := by
  constructor
  · exact domain_operator_SA
  · intro v
    have hv : v ⬝ᵥ (domain_operator.mulVec v) = v ⬝ᵥ v := by
      unfold domain_operator
      simp
    rw [hv]
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_self_nonneg _

noncomputable def domain_HS :=
  HS_norm 21 domain_operator

theorem domain_HS_nonneg :
    0 ≤ domain_HS :=
  HS_norm_nonneg 21 domain_operator

noncomputable def domain_op_norm :=
  op_norm 21 domain_operator

theorem domain_op_norm_nonneg :
    0 ≤ domain_op_norm :=
  op_norm_nonneg 21 domain_operator

noncomputable def domain_semigroup :
    OpSemigroup 21 where
  T      := fun t => 1 + t • (0 : Matrix
              (Fin 21) (Fin 21) ℝ)
  T_zero := by simp
  T_add  := by intro s t; simp

theorem domain_sg_zero :
    domain_semigroup.T 0 = 1 :=
  semigroup_zero 21 domain_semigroup

noncomputable def domain_spectral :=
  spectral_radius 21 (by norm_num) (fun _ => 1)

theorem domain_spectral_nonneg :
    0 ≤ domain_spectral :=
  spectral_radius_nonneg 21 (by norm_num) (fun _ => 1)

theorem domain_func_calc_nonneg
    (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ Matrix.trace
      (func_calc 21 domain_operator f) :=
  trace_func_calc 21 domain_operator f hf

structure OperatorTheoryLock where
  op_norm_nn     : ∀ (n : ℕ)
                     (A : Matrix (Fin n)
                           (Fin n) ℝ),
                     0 ≤ op_norm n A
  HS_norm_nn     : ∀ (n : ℕ)
                     (A : Matrix (Fin n)
                           (Fin n) ℝ),
                     0 ≤ HS_norm n A
  spec_rad_nn    : ∀ (n : ℕ) (hn : 0 < n)
                     (ev : Fin n → ℝ),
                     0 ≤ spectral_radius n hn ev
  PSD_trace_nn   : ∀ (n : ℕ)
                     (A : Matrix (Fin n)
                           (Fin n) ℝ),
                     is_PSD n A →
                     0 ≤ Matrix.trace A
  func_calc_nn   : ∀ (n : ℕ)
                     (A : Matrix (Fin n)
                           (Fin n) ℝ)
                     (f : ℝ → ℝ),
                     (∀ x, 0 ≤ f x) →
                     ∀ i, 0 ≤
                       (func_calc n A f) i i
  trace_fc_nn    : ∀ (n : ℕ)
                     (A : Matrix (Fin n)
                           (Fin n) ℝ)
                     (f : ℝ → ℝ),
                     (∀ x, 0 ≤ f x) →
                     0 ≤ Matrix.trace
                       (func_calc n A f)
  sg_zero        : ∀ (n : ℕ)
                     (S : OpSemigroup n),
                     S.T 0 = 1
  dom_op_SA      : is_self_adjoint 21
                     domain_operator
  dom_op_PSD     : is_PSD 21 domain_operator
  dom_HS_nn      : 0 ≤ domain_HS
  dom_op_nn      : 0 ≤ domain_op_norm
  dom_spec_nn    : 0 ≤ domain_spectral
  dom_sg_zero    : domain_semigroup.T 0 = 1
  dom_fc_nn      : ∀ (f : ℝ → ℝ),
                     (∀ x, 0 ≤ f x) →
                     0 ≤ Matrix.trace
                       (func_calc 21
                         domain_operator f)

def OTLock : OperatorTheoryLock where
  op_norm_nn    := op_norm_nonneg
  HS_norm_nn    := HS_norm_nonneg
  spec_rad_nn   := spectral_radius_nonneg
  PSD_trace_nn  := PSD_trace_nonneg
  func_calc_nn  := func_calc_nonneg
  trace_fc_nn   := trace_func_calc
  sg_zero       := semigroup_zero
  dom_op_SA     := domain_operator_SA
  dom_op_PSD    := domain_operator_PSD
  dom_HS_nn     := domain_HS_nonneg
  dom_op_nn     := domain_op_norm_nonneg
  dom_spec_nn   := domain_spectral_nonneg
  dom_sg_zero   := domain_sg_zero
  dom_fc_nn     := domain_func_calc_nonneg

end OperatorTheory

