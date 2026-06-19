import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open LinearMap Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

structure DensityOperator where
  op           : H →L[ℂ] H
  is_pos       : Matrix.PositiveSemidefinite op
  is_trace_one : trace ℂ H op = 1

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

structure CPTP (n : ℕ) where
  kraus            : List (Mat n)
  is_complete      : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map {n : ℕ} (Φ : CPTP n) (a : Mat n) : Mat n :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving {n : ℕ} (Φ : CPTP n) (a : Mat n) :
  Matrix.trace (cptp_map Φ a) = Matrix.trace a := by
  simp [cptp_map, Matrix.trace_sum, Matrix.trace_mul_cycle, Φ.is_complete]

lemma cptp_is_cp {n : ℕ} (Φ : CPTP n) (a : Mat n) (ha : Matrix.PositiveSemidefinite a) :
  Matrix.PositiveSemidefinite (cptp_map Φ a) := by
  unfold cptp_map
  induction Φ.kraus with
  | nil => simp; exact posSemidef_zero
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Matrix.PositiveSemidefinite.add _ ih
    exact Matrix.PositiveSemidefinite.mul_conjTranspose_self k ha

structure UnitaryOperator where
  op         : H →L[ℂ] H
  is_unitary : op ∈ unitary (H →L[ℂ] H)

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
  trace ℂ H (U.op * ρ.op * U.op.adjoint) = trace ℂ H ρ.op := by
  simp only [LinearMap.trace_mul_comm]
  rw [LinearMap.trace_mul_comm U.op (ρ.op * U.op.adjoint), ← mul_assoc]
  have hUU : U.op.adjoint * U.op = 1 := by exact_mod_cast U.is_unitary.star_mul_self
  rw [hUU, one_mul]

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
  Matrix.PositiveSemidefinite (U.op * ρ.op * U.op.adjoint) := by
  intro v
  exact ρ.is_pos (U.op.adjoint v)

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator), trace ℂ H (U.op * ρ.op * U.op.adjoint) = trace ℂ H ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator), Matrix.PositiveSemidefinite (U.op * ρ.op * U.op.adjoint)
  cptp_trace_law : ∀ (n : ℕ) (Φ : CPTP n) (a : Mat n), Matrix.trace (cptp_map Φ a) = Matrix.trace a
  cptp_positivity : ∀ (n : ℕ) (Φ : CPTP n) (a : Mat n), Matrix.PositiveSemidefinite a → Matrix.PositiveSemidefinite (cptp_map Φ a)

def certify : CertifiedKernel where
  trace_invariant         := trace_unitary_invariance
  positivity_preservation := wigner_symmetry
  cptp_trace_law          := cptp_trace_preserving
  cptp_positivity         := cptp_is_cp

end Matrix7

