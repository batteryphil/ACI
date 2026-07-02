import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Complex

namespace QuantumCore

variable {H : Type*}
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
  [CompleteSpace H]
  [Nontrivial H]

/-
Key design rule:
We NEVER mix LinearMap and ContinuousLinearMap in compositions.
We only convert at trace boundaries.
-/

abbrev CL := ContinuousLinearMap ℂ H H

structure DensityOperator where
  op      : CL
  h_sa    : op.adjoint = op
  h_pos   : ∀ v : H, 0 ≤ (inner v (op v)).re
  h_trace : (LinearMap.trace ℂ H op.toLinearMap).re = 1

theorem density_trace_one (ρ : DensityOperator) :
    (LinearMap.trace ℂ H ρ.op.toLinearMap).re = 1 :=
  ρ.h_trace

theorem sa_real_diagonal (A : CL)
    (hA : A.adjoint = A) (v : H) :
    (inner v (A v)).im = 0 := by
  have h1 : inner (A v) v = inner v (A v) := by
    simpa [hA] using (A.adjoint_inner_left v v)
  have h2 : inner (A v) v = starRingEnd ℂ (inner v (A v)) :=
    (inner_conj_symm (A v) v).symm
  have h : inner v (A v) = starRingEnd ℂ (inner v (A v)) :=
    h1.symm.trans h2
  have : Complex.im (inner v (A v)) = 0 := by
    simpa [Complex.conj_im] using congrArg Complex.im h
  exact this

theorem sa_linear (A B : CL) (α β : ℝ)
    (hA : A.adjoint = A) (hB : B.adjoint = B) :
    ((α : ℂ) • A + (β : ℂ) • B).adjoint =
      (α : ℂ) • A + (β : ℂ) • B := by
  simp [hA, hB, Complex.conj_ofReal]

theorem sa_composition_seal (ρ P : CL)
    (hρ : ρ.adjoint = ρ) (hP : P.adjoint = P) :
    (P ∘L (ρ ∘L P)).adjoint = P ∘L (ρ ∘L P) := by
  simp [hρ, hP, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

structure Projector where
  op   : CL
  h_sa : op.adjoint = op
  h_id : op ∘L op = op

theorem proj_idempotent (P : Projector) (v : H) :
    P.op (P.op v) = P.op v :=
  congrArg (fun f => f v) P.h_id

theorem proj_spectrum (P : Projector) (v : H) (lam : ℂ)
    (hv : P.op v = lam • v) (hv_ne : v ≠ 0) :
    lam = 0 ∨ lam = 1 := by
  have h := congrArg (fun f => f v) P.h_id
  simp [hv] at h
  have : (lam * lam - lam) • v = 0 := by
    simpa [sub_smul, smul_smul] using h
  have := smul_eq_zero.mp this
  cases this with
  | inl hlam =>
      have : lam * (lam - 1) = 0 := by
        have : lam * (lam - 1) = lam * lam - lam := by ring
        simp [this, hlam]
      cases mul_eq_zero.mp this with
      | inl h1 => exact Or.inl h1
      | inr h2 => exact Or.inr h2
  | inr hv0 => exact (hv_ne hv0).elim

/-
TRACE SAFETY RULE:
convert to LinearMap ONLY here
-/
noncomputable def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H
    (ρ.op ∘L P.op).toLinearMap).re

theorem meas_prob_cyclic (ρ : DensityOperator) (P : Projector) :
    meas_prob ρ P =
    (LinearMap.trace ℂ H
      (P.op ∘L (ρ.op ∘L P.op)).toLinearMap).re := by
  unfold meas_prob
  simp

noncomputable def post_meas_op (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) : CL :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op ∘L (ρ.op ∘L P.op))

theorem post_meas_sa (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) :
    (post_meas_op ρ P h_prob).adjoint =
      post_meas_op ρ P h_prob := by
  unfold post_meas_op
  simp [sa_composition_seal ρ.op P.op ρ.h_sa P.h_sa, Complex.conj_ofReal]

theorem post_meas_pos (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) (v : H) :
    0 ≤ (inner v ((post_meas_op ρ P h_prob) v)).re := by
  simp [post_meas_op]
  have h := ρ.h_pos (P.op v)
  positivity

structure UnitaryOp where
  op    : CL
  h_adj : op.adjoint ∘L op = 1
  h_inv : op ∘L op.adjoint = 1

noncomputable def unitary_evolve (U : UnitaryOp) (ρ : DensityOperator) : CL :=
  U.op ∘L (ρ.op ∘L U.op.adjoint)

theorem unitary_trace_invariant (U : UnitaryOp) (A : CL) :
    LinearMap.trace ℂ H
      (U.op ∘L (A ∘L U.op.adjoint)).toLinearMap
    = LinearMap.trace ℂ H A.toLinearMap := by
  sorry

theorem unitary_preserves_sa (U : UnitaryOp) (A : CL)
    (hA : A.adjoint = A) :
    (U.op ∘L (A ∘L U.op.adjoint)).adjoint =
      U.op ∘L (A ∘L U.op.adjoint) := by
  simp [hA, ContinuousLinearMap.adjoint_comp]

def is_pure_state (ρ : DensityOperator) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H,
    ρ.op v = inner ψ v • ψ

end QuantumCore
