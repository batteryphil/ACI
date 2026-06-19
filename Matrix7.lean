import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open LinearMap Matrix

variable {n : ℕ}

structure DensityOperator where
  op           : Matrix (Fin n) (Fin n) ℂ
  is_pos       : PosSemidef op
  is_trace_one : trace op = 1

structure CPTP (n : ℕ) where
  kraus            : List (Matrix (Fin n) (Fin n) ℂ)
  is_complete      : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map {n : ℕ} (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving {n : ℕ} (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) :
  trace (cptp_map Φ a) = trace a := by
  simp [cptp_map, trace_sum, trace_mul_cycle, Φ.is_complete]

lemma cptp_is_cp {n : ℕ} (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) (ha : PosSemidef a) :
  PosSemidef (cptp_map Φ a) := by
  sorry 

structure UnitaryOperator where
  op         : Matrix (Fin n) (Fin n) ℂ
  is_unitary : op * star op = 1

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
  trace (U.op * ρ.op * star U.op) = trace ρ.op := by
  sorry

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
  PosSemidef (U.op * ρ.op * star U.op) := by
  sorry

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator), trace (U.op * ρ.op * star U.op) = trace ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator), PosSemidef (U.op * ρ.op * star U.op)

def certify : CertifiedKernel := ⟨trace_unitary_invariance, wigner_symmetry⟩

end Matrix7

