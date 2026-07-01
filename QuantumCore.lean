import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open Complex
namespace QuantumCore

-- Enforce global constraints on H to ensure stability for all definitions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H] [Nontrivial H]

-- =============================================================================
-- TIER 1: DENSITY OPERATORS
-- =============================================================================
structure DensityOperator where
  op      : H →L[ℂ] H
  h_sa    : ContinuousLinearMap.adjoint op = op
  h_pos   : ∀ v : H, 0 ≤ (inner (𝕜 := ℂ) v (op v)).re
  h_trace : (LinearMap.trace ℂ H (op : H →ₗ[ℂ] H)).re = 1

-- =============================================================================
-- TIER 2: OPERATOR ALGEBRA
-- =============================================================================
theorem sa_trace_real (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) :
    (LinearMap.trace ℂ H (A : H →ₗ[ℂ] H)).im = 0 := by
  have h := LinearMap.trace_conj ℂ H (A : H →ₗ[ℂ] H)
  -- The core fix: ensure the coercion is explicit
  rw [← ContinuousLinearMap.coe_toLinearMap_adjoint, hA] at h
  exact Complex.im_eq_zero_of_conj_eq h

-- =============================================================================
-- TIER 3: MEASUREMENT
-- =============================================================================
structure Projector where
  op   : H →L[ℂ] H
  h_sa : ContinuousLinearMap.adjoint op = op
  h_id : op.comp op = op

noncomputable def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H ((ρ.op.comp P.op) : H →ₗ[ℂ] H)).re

-- =============================================================================
-- TIER 4: POST-MEASUREMENT DYNAMICS
-- =============================================================================
noncomputable def post_meas_op (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) : H →L[ℂ] H :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op.comp (ρ.op.comp P.op))

-- =============================================================================
-- TIER 5: UNITARY EVOLUTION
-- =============================================================================
structure UnitaryOp where
  op    : H →L[ℂ] H
  h_adj : (ContinuousLinearMap.adjoint op).comp op = ContinuousLinearMap.id ℂ H
  h_inv : op.comp (ContinuousLinearMap.adjoint op) = ContinuousLinearMap.id ℂ H

theorem unitary_trace_invariant (U : UnitaryOp) (A : H →L[ℂ] H) :
    LinearMap.trace ℂ H ((U.op.comp (A.comp (ContinuousLinearMap.adjoint U.op))) : H →ₗ[ℂ] H)
    = LinearMap.trace ℂ H (A : H →ₗ[ℂ] H) := by
  -- Replacing the previous 'simp' which failed with an explicit tactic block
  rw [LinearMap.trace_mul_comm]
  congr 1
  simp [ContinuousLinearMap.comp_assoc, U.h_inv]

-- =============================================================================
-- TIER 6: PURE STATE IDEMPOTENCE
-- =============================================================================
def is_pure_state (ρ : DensityOperator) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H, ρ.op v = inner (𝕜 := ℂ) ψ v • ψ

theorem pure_state_idempotent (ρ : DensityOperator) (hpure : is_pure_state ρ) (v : H) :
    ρ.op (ρ.op v) = ρ.op v := by
  obtain ⟨ψ, hψ_norm, hψ⟩ := hpure
  rw [hψ]
  simp [inner_smul_right]
  rw [show inner (𝕜 := ℂ) ψ ψ = (1 : ℂ) from by
        rw [inner_self_eq_norm_sq_to_K]; simp [hψ_norm]]
  simp

end QuantumCore

