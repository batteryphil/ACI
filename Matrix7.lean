import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open Matrix

structure DensityOperator (n : ℕ) where
  op : Matrix (Fin n) (Fin n) ℂ
  is_pos : op.PosSemidef
  is_trace_one : op.trace = 1

structure UnitaryOperator (n : ℕ) where
  op : Matrix (Fin n) (Fin n) ℂ
  is_unitary_right : op * star op = 1
  is_unitary_left : star op * op = 1

theorem trace_unitary_invariance {n : ℕ} (U : UnitaryOperator n) (ρ : DensityOperator n) :
    (U.op * ρ.op * star U.op).trace = ρ.op.trace := by
  have h : (U.op * ρ.op * star U.op).trace = (ρ.op * (star U.op * U.op)).trace := by
    rw [← Matrix.trace_mul_comm]
    ring_nf
  rw [h, U.is_unitary_left, mul_one]

theorem wigner_symmetry {n : ℕ} (U : UnitaryOperator n) (ρ : DensityOperator n) :
    (U.op * ρ.op * star U.op).PosSemidef :=
  ρ.is_pos.mul_mul_conjTranspose_same U.op

structure CertifiedKernel (n : ℕ) where
  trace_invariant : ∀ (U : UnitaryOperator n) (ρ : DensityOperator n),
    (U.op * ρ.op * star U.op).trace = ρ.op.trace
  positivity_preservation : ∀ (U : UnitaryOperator n) (ρ : DensityOperator n),
    (U.op * ρ.op * star U.op).PosSemidef

def certify (n : ℕ) : CertifiedKernel n where
  trace_invariant := trace_unitary_invariance
  positivity_preservation := wigner_symmetry

end Matrix7
