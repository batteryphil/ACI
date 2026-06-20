import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open Matrix

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

structure DensityOperator where
  op : Matrix (Fin n) (Fin n) ℂ
  is_pos : PosSemidef op
  is_trace_one : trace op = 1

structure CPTP (n : ℕ) [Fintype (Fin n)] [DecidableEq (Fin n)] where
  kraus : List (Matrix (Fin n) (Fin n) ℂ)
  is_complete : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) :
    trace (cptp_map Φ a) = trace a := by
  simp [cptp_map, trace_sum, trace_mul_cycle]
  rw [← Matrix.sum_eq_list_sum, ← trace_sum, ← Matrix.mul_sum, Φ.is_complete, one_mul]

structure UnitaryOperator where
  op : Matrix (Fin n) (Fin n) ℂ
  is_unitary : op * star op = 1

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
    trace (U.op * ρ.op * star U.op) = trace ρ.op := by
  rw [trace_mul_cycle, ← mul_assoc, U.is_unitary, one_mul]

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
    PosSemidef (U.op * ρ.op * star U.op) :=
  ρ.is_pos.conj_transpose_mul_self U.op

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator),
    trace (U.op * ρ.op * star U.op) = trace ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator),
    PosSemidef (U.op * ρ.op * star U.op)

def certify : CertifiedKernel where
  trace_invariant := trace_unitary_invariance
  positivity_preservation := wigner_symmetry

end Matrix7
