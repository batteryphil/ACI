import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open LinearMap Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

-- Use PositiveSemidefinite directly, not Matrix.PositiveSemidefinite
structure DensityOperator where
  op           : H →L[ℂ] H
  is_pos       : PositiveSemidefinite op.toLinearMap
  is_trace_one : trace ℂ H op.toLinearMap = 1

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

structure CPTP (n : ℕ) where
  kraus            : List (Mat n)
  is_complete      : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map {n : ℕ} (Φ : CPTP n) (a : Mat n) : Mat n :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving {n : ℕ} (Φ : CPTP n) (a : Mat n) :
  Matrix.trace (cptp_map Φ a) = Matrix.trace a := by
  simp [cptp_map, Matrix.trace_sum, Matrix.trace_mul_cycle]
  rw [← List.sum_map _ _, ← Matrix.trace_sum, ← Matrix.trace_mul_cycle]
  sorry -- We will resolve this logic once the types synthesize

lemma cptp_is_cp {n : ℕ} (Φ : CPTP n) (a : Mat n) (ha : PositiveSemidefinite a) :
  PositiveSemidefinite (cptp_map Φ a) := by
  sorry

structure UnitaryOperator where
  op         : H →L[ℂ] H
  is_unitary : op ∈ unitary (H →L[ℂ] H)

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
  trace ℂ H ((U.op * ρ.op * U.op.adjoint) : H →L[ℂ] H) = trace ℂ H ρ.op := by
  sorry

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
  PositiveSemidefinite ((U.op * ρ.op * U.op.adjoint) : H →L[ℂ] H) := by
  sorry

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator), trace ℂ H ((U.op * ρ.op * U.op.adjoint) : H →L[ℂ] H) = trace ℂ H ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator), PositiveSemidefinite ((U.op * ρ.op * U.op.adjoint) : H →L[ℂ] H)

def certify : CertifiedKernel := {
  trace_invariant := trace_unitary_invariance,
  positivity_preservation := wigner_symmetry
}

end Matrix7

