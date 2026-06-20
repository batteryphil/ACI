  mport Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open LinearMap Matrix

variable {n : Nat} 

structure DensityOperator where
  op : Matrix (Fin n) (Fin n) Complex
  is_pos : PosSemidef op
  is_trace_one : trace op = 1

structure CPTP (n : Nat) where
  kraus : List (Matrix (Fin n) (Fin n) Complex)
  is_complete : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) Complex) : Matrix (Fin n) (Fin n) Complex :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) Complex) :
  trace (cptp_map Φ a) = trace a := by
  simp [cptp_map, trace_sum, trace_mul_cycle]
  rw [← Matrix.mul_sum, Φ.is_complete, one_mul]

lemma cptp_is_cp (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) Complex) (ha : PosSemidef a) :
  PosSemidef (cptp_map Φ a) := by
  apply PosSemidef.sum
  intro k _
  exact PosSemidef.mul_star_mul ha k

structure UnitaryOperator where
  op : Matrix (Fin n) (Fin n) Complex
  is_unitary : op * star op = 1

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
  trace (U.op * ρ.op * star U.op) = trace ρ.op := by
  rw [trace_mul_cycle, trace_mul_cycle, U.is_unitary, one_mul]

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
  PosSemidef (U.op * ρ.op * star U.op) := by
  apply PosSemidef.congr (U.op * ρ.op * star U.op) (U.op * ρ.op * star U.op)
  apply PosSemidef.conj ρ.is_pos U.op

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator), trace (U.op * ρ.op * star U.op) = trace ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator), PosSemidef (U.op * ρ.op * star U.op)

def certify : CertifiedKernel := ⟨trace_unitary_invariance, wigner_symmetry⟩
end Matrix7

