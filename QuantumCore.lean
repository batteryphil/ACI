import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# QUANTUMCORE: ACI SOVEREIGN QUANTUM OPERATOR ENGINE
## Full Unified Production Build: Single & Composite System Dynamics
-/

open Complex TensorProduct

namespace QuantumCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H] [Nontrivial H]

-- =============================================================================
-- TIER 1: CORE DENSITY OPERATOR SPECIFICATION
-- =============================================================================
structure DensityOperator where
  op      : H →L[ℂ] H
  h_sa    : ContinuousLinearMap.adjoint op = op
  h_pos   : ∀ v : H, 0 ≤ (inner (𝕜 := ℂ) v (op v)).re
  h_trace : (LinearMap.trace ℂ H op.toLinearMap).re = 1

-- =============================================================================
-- TIER 2: MEASUREMENT AND TRANSITION DYNAMICS
-- =============================================================================
structure Projector where
  op   : H →L[ℂ] H
  h_sa : ContinuousLinearMap.adjoint op = op
  h_id : op.comp op = op

noncomputable def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H (ρ.op.comp P.op).toLinearMap).re

noncomputable def post_meas_op (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) : H →L[ℂ] H :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op.comp (ρ.op.comp P.op))

-- =============================================================================
-- TIER 3: UNITARY EVOLUTION AND ENTANGLEMENT STRUCTURE
-- =============================================================================
structure UnitaryOp where
  op    : H →L[ℂ] H
  h_adj : (ContinuousLinearMap.adjoint op).comp op = ContinuousLinearMap.id ℂ H
  h_inv : op.comp (ContinuousLinearMap.adjoint op) = ContinuousLinearMap.id ℂ H

def is_pure_state (ρ : DensityOperator) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H, ρ.op v = inner (𝕜 := ℂ) ψ v • ψ

-- =============================================================================
-- TIER 4: COMPOSITE SYSTEM FORMALISM (TENSOR PRODUCT SPACE)
-- =============================================================================
variable {H1 H2 : Type*} [InnerProductSpace ℂ H1] [InnerProductSpace ℂ H2]
  [FiniteDimensional ℂ H1] [FiniteDimensional ℂ H2]

/-- The partial trace allows for the definition of reduced density matrices
    necessary for calculating entanglement entropy. -/
noncomputable def partial_trace_left (ρ : (H1 ⊗[ℂ] H2) →L[ℂ] (H1 ⊗[ℂ] H2)) : H1 →L[ℂ] H1 :=
  -- This maps the full density operator to the reduced state of system 1.
  -- Implemented via trace over the second Hilbert space component.
  (LinearMap.ltrace ℂ H2 H2).toContinuousLinearMap.comp (ContinuousLinearMap.tensorRight ℂ ρ)

-- =============================================================================
-- TIER 5: APEX THEOREMS
-- =============================================================================
theorem unitary_trace_invariant (U : UnitaryOp) (A : H →L[ℂ] H) :
    LinearMap.trace ℂ H (U.op.comp (A.comp (ContinuousLinearMap.adjoint U.op))).toLinearMap
    = LinearMap.trace ℂ H A.toLinearMap := by
  rw [LinearMap.trace_mul_comm, ← ContinuousLinearMap.comp_assoc, U.h_inv]
  simp [ContinuousLinearMap.id_comp]

theorem sa_product_trace_real (A B : H →L[ℂ] H)
    (hA : ContinuousLinearMap.adjoint A = A) (hB : ContinuousLinearMap.adjoint B = B) :
    (LinearMap.trace ℂ H (A.comp B).toLinearMap).im = 0 := by
  have h_prod_sa : ContinuousLinearMap.adjoint (A.comp B) = B.comp A := by
    rw [ContinuousLinearMap.adjoint_comp, hA, hB]
  have h_trace_eq : LinearMap.trace ℂ H (A.comp B).toLinearMap = 
                    starRingEnd ℂ (LinearMap.trace ℂ H (A.comp B).toLinearMap) := by
    rw [← LinearMap.trace_adjoint (A.comp B).toLinearMap, 
        ← ContinuousLinearMap.coe_toLinearMap_adjoint, h_prod_sa]
    exact LinearMap.trace_mul_comm ℂ B.toLinearMap A.toLinearMap
  exact Complex.im_eq_zero_of_conj_eq h_trace_eq

end QuantumCore


