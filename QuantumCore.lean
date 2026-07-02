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

abbrev CL := ContinuousLinearMap ℂ H H

structure DensityOperator where
  op      : CL
  h_sa    : op.adjoint = op
  h_pos   : ∀ v : H, 0 ≤ (inner v (op v)).re
  h_trace : (LinearMap.trace ℂ H op.toLinearMap).re = 1

structure Projector where
  op   : CL
  h_sa : op.adjoint = op
  h_id : op ∘L op = op

structure UnitaryOp where
  op    : CL
  h_adj : op.adjoint ∘L op = 1
  h_inv : op ∘L op.adjoint = 1

/-
========================
CORE TRACE LEMMA BLOCK
========================
-/

lemma trace_cyclic₂ (A B : CL) :
    LinearMap.trace ℂ H (A ∘L B).toLinearMap
    = LinearMap.trace ℂ H (B ∘L A).toLinearMap := by
  simpa using
    (LinearMap.trace_mul_comm ℂ A.toLinearMap B.toLinearMap)

/-
========================
MEASUREMENT
========================
-/

noncomputable def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H (ρ.op ∘L P.op).toLinearMap).re

theorem meas_prob_cyclic (ρ : DensityOperator) (P : Projector) :
    meas_prob ρ P =
    (LinearMap.trace ℂ H (P.op ∘L (ρ.op ∘L P.op)).toLinearMap).re := by
  unfold meas_prob
  simp [trace_cyclic₂]

noncomputable def post_meas_op (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) : CL :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op ∘L (ρ.op ∘L P.op))

/-
========================
SELF-ADJOINTNESS
========================
-/

theorem post_meas_sa (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) :
    (post_meas_op ρ P h_prob).adjoint =
      post_meas_op ρ P h_prob := by
  unfold post_meas_op
  simp [ρ.h_sa, P.h_sa, ContinuousLinearMap.adjoint_comp, Complex.conj_ofReal]

/-
========================
POSITIVITY (STRUCTURAL)
========================
-/

theorem post_meas_pos (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) (v : H) :
    0 ≤ (inner v ((post_meas_op ρ P h_prob) v)).re := by
  classical
  unfold post_meas_op
  have hρ := ρ.h_pos (P.op v)
  have hscale : (0 : ℝ) ≤ 1 / meas_prob ρ P := by
    exact le_of_lt (by simpa using h_prob)
  positivity

/-
========================
UNITARY EVOLUTION
========================
-/

noncomputable def unitary_evolve (U : UnitaryOp) (ρ : DensityOperator) : CL :=
  U.op ∘L (ρ.op ∘L U.op.adjoint)

theorem unitary_trace_invariant (U : UnitaryOp) (A : CL) :
    LinearMap.trace ℂ H
      (U.op ∘L (A ∘L U.op.adjoint)).toLinearMap
    = LinearMap.trace ℂ H A.toLinearMap := by
  classical
  -- Expand into LinearMap world
  have hU1 :
      U.op.toLinearMap.comp U.op.adjoint.toLinearMap = LinearMap.id := by
    simpa using congrArg ContinuousLinearMap.toLinearMap U.h_inv

  have hU2 :
      U.op.adjoint.toLinearMap.comp U.op.toLinearMap = LinearMap.id := by
    simpa using congrArg ContinuousLinearMap.toLinearMap U.h_adj

  calc
    LinearMap.trace ℂ H (U.op ∘L (A ∘L U.op.adjoint)).toLinearMap
        = LinearMap.trace ℂ H
            (U.op.toLinearMap.comp (A.toLinearMap.comp U.op.adjoint.toLinearMap)) := by rfl
    _ = LinearMap.trace ℂ H
            ((A.toLinearMap.comp U.op.adjoint.toLinearMap).comp U.op.toLinearMap) := by
        simpa using
          (LinearMap.trace_mul_comm ℂ U.op.toLinearMap
            (A.toLinearMap.comp U.op.adjoint.toLinearMap))
    _ = LinearMap.trace ℂ H
            (A.toLinearMap.comp (U.op.adjoint.toLinearMap.comp U.op.toLinearMap)) := by
        simp [LinearMap.comp_assoc]
    _ = LinearMap.trace ℂ H A.toLinearMap := by
        simp [hU2, LinearMap.comp_id, LinearMap.id_comp]

theorem unitary_preserves_sa (U : UnitaryOp) (A : CL)
    (hA : A.adjoint = A) :
    (U.op ∘L (A ∘L U.op.adjoint)).adjoint =
      U.op ∘L (A ∘L U.op.adjoint) := by
  simp [hA, ContinuousLinearMap.adjoint_comp]

/-
========================
PURE STATES
========================
-/

def is_pure_state (ρ : DensityOperator) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H,
    ρ.op v = inner ψ v • ψ

end QuantumCore
