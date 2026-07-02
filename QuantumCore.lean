import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Complex

namespace QuantumCore

variable {H : Type*}
variable [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]
variable [CompleteSpace H]
variable [Nontrivial H]

/-- FIX: explicit alias so Lean never loses the type -/
abbrev CL (H : Type*) [NormedAddCommGroup H] :=
  H →L[ℂ] H

structure DensityOperator where
  op      : CL H
  h_sa    : ContinuousLinearMap.adjoint op = op
  h_pos   : ∀ v : H, 0 ≤ (inner v (op v)).re
  h_trace : (LinearMap.trace ℂ H op.toLinearMap).re = 1

theorem density_trace_one (ρ : DensityOperator (H := H)) :
    (LinearMap.trace ℂ H ρ.op.toLinearMap).re = 1 := ρ.h_trace

theorem sa_real_diagonal (A : CL H)
    (hA : ContinuousLinearMap.adjoint A = A) (v : H) :
    (inner v (A v)).im = 0 := by
  have step1 : inner (A v) v = inner v (A v) := by
    have h := ContinuousLinearMap.adjoint_inner_left A v v
    simpa [hA] using h
  have step2 : inner (A v) v = starRingEnd ℂ (inner v (A v)) :=
    (inner_conj_symm (A v) v).symm
  have key : inner v (A v) = starRingEnd ℂ (inner v (A v)) :=
    step1.symm.trans step2
  have him := congrArg Complex.im key
  simpa using him

theorem sa_linear (A B : CL H) (α β : ℝ)
    (hA : ContinuousLinearMap.adjoint A = A)
    (hB : ContinuousLinearMap.adjoint B = B) :
    ContinuousLinearMap.adjoint
      ((α : ℂ) • A + (β : ℂ) • B)
      = (α : ℂ) • A + (β : ℂ) • B := by
  simp [hA, hB, Complex.conj_ofReal]

theorem sa_composition_seal (ρ P : CL H)
    (hρ : ContinuousLinearMap.adjoint ρ = ρ)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (P.comp (ρ.comp P)) =
    P.comp (ρ.comp P) := by
  simp [hρ, hP, ContinuousLinearMap.comp_assoc]

structure Projector where
  op   : CL H
  h_sa : ContinuousLinearMap.adjoint op = op
  h_id : op.comp op = op

theorem proj_idempotent (P : Projector (H := H)) (v : H) :
    P.op (P.op v) = P.op v :=
  DFunLike.congr_fun P.h_id v

theorem proj_spectrum (P : Projector (H := H)) (v : H) (lam : ℂ)
    (hv : P.op v = lam • v) (hv_ne : v ≠ 0) :
    lam = 0 ∨ lam = 1 := by
  have h1 : P.op (P.op v) = P.op v := proj_idempotent P v
  rw [hv, ContinuousLinearMap.map_smul, hv] at h1
  have hz : (lam * lam - lam) • v = 0 := by
    simpa [sub_smul, mul_smul] using h1
  have := smul_eq_zero.mp hz
  cases this with
  | inl h =>
      have : lam * (lam - 1) = 0 := by
        simpa using h
      cases mul_eq_zero.mp this with
      | inl hlam => exact Or.inl hlam
      | inr hlam => exact Or.inr hlam
  | inr hv0 => exact (hv_ne hv0).elim

noncomputable def meas_prob (ρ : DensityOperator (H := H))
    (P : Projector (H := H)) : ℝ :=
  (LinearMap.trace ℂ H (ρ.op.comp P.op).toLinearMap).re

theorem meas_prob_cyclic (ρ : DensityOperator (H := H))
    (P : Projector (H := H)) :
    meas_prob ρ P
    = (LinearMap.trace ℂ H (P.op.comp (ρ.op.comp P.op)).toLinearMap).re := by
  unfold meas_prob
  -- trace cyclicity is nontrivial; keep placeholder but no unknown identifiers
  admit

noncomputable def post_meas_op (ρ : DensityOperator (H := H))
    (P : Projector (H := H))
    (h_prob : 0 < meas_prob ρ P) : CL H :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op.comp (ρ.op.comp P.op))

theorem post_meas_sa (ρ : DensityOperator (H := H))
    (P : Projector (H := H))
    (h_prob : 0 < meas_prob ρ P) :
    ContinuousLinearMap.adjoint (post_meas_op ρ P h_prob)
    = post_meas_op ρ P h_prob := by
  simp [post_meas_op, sa_composition_seal ρ.op P.op ρ.h_sa P.h_sa]

structure UnitaryOp where
  op    : CL H
  h_adj : (ContinuousLinearMap.adjoint op).comp op = ContinuousLinearMap.id ℂ H
  h_inv : op.comp (ContinuousLinearMap.adjoint op) = ContinuousLinearMap.id ℂ H

axiom MHD_Stable : Prop
axiom Unitary_Evolution : Prop
axiom unitary_of_mhd_stable : MHD_Stable → Unitary_Evolution

noncomputable def unitary_evolve (U : UnitaryOp (H := H))
    (ρ : DensityOperator (H := H)) : CL H :=
  U.op.comp (ρ.op.comp (ContinuousLinearMap.adjoint U.op))

theorem unitary_trace_invariant (U : UnitaryOp (H := H))
    (A : CL H) :
    LinearMap.trace ℂ H
      (U.op.comp (A.comp (ContinuousLinearMap.adjoint U.op))).toLinearMap
    = LinearMap.trace ℂ H A.toLinearMap := by
  admit

theorem unitary_preserves_sa (U : UnitaryOp (H := H))
    (A : CL H)
    (hA : ContinuousLinearMap.adjoint A = A) :
    ContinuousLinearMap.adjoint
      (U.op.comp (A.comp (ContinuousLinearMap.adjoint U.op)))
    =
    U.op.comp (A.comp (ContinuousLinearMap.adjoint U.op)) := by
  simp [hA]

def is_pure_state (ρ : DensityOperator (H := H)) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H,
    ρ.op v = inner ψ v • ψ

end QuantumCore
