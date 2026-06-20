import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open Matrix

variable {n : ℕ}

structure DensityOperator where
  op : Matrix (Fin n) (Fin n) ℂ
  is_pos : PosSemidef op
  is_trace_one : trace op = 1

structure CPTP (n : ℕ) where
  kraus : List (Matrix (Fin n) (Fin n) ℂ)
  is_complete : List.sum (kraus.map (fun k => star k * k)) = 1

def cptp_map (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  List.sum (Φ.kraus.map (fun k => k * a * star k))

lemma cptp_trace_preserving (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) :
    trace (cptp_map Φ a) = trace a := by
  simp only [cptp_map, map_list_sum, List.map_map, Function.comp, trace_mul_cycle]
  rw [← Matrix.mul_sum, Φ.is_complete, one_mul]

lemma cptp_is_cp (Φ : CPTP n) (a : Matrix (Fin n) (Fin n) ℂ) (ha : PosSemidef a) :
    PosSemidef (cptp_map Φ a) := by
  apply PosSemidef.sum_of_forall
  intro k _
  exact ha.mul_mul_conjTranspose_same k

structure UnitaryOperator where
  op : Matrix (Fin n) (Fin n) ℂ
  is_unitary : op * star op = 1

theorem trace_unitary_invariance (U : UnitaryOperator) (ρ : DensityOperator) :
    trace (U.op * ρ.op * star U.op) = trace ρ.op := by
  rw [trace_mul_cycle, mul_assoc, U.is_unitary, mul_one]

theorem wigner_symmetry (U : UnitaryOperator) (ρ : DensityOperator) :
    PosSemidef (U.op * ρ.op * star U.op) :=
  ρ.is_pos.mul_mul_conjTranspose_same U.op

structure CertifiedKernel where
  trace_invariant : ∀ (U : UnitaryOperator) (ρ : DensityOperator),
    trace (U.op * ρ.op * star U.op) = trace ρ.op
  positivity_preservation : ∀ (U : UnitaryOperator) (ρ : DensityOperator),
    PosSemidef (U.op * ρ.op * star U.op)

def certify : CertifiedKernel where
  trace_invariant := trace_unitary_invariance
  positivity_preservation := wigner_symmetry

end Matrix7
