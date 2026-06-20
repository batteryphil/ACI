import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

namespace Matrix7
open Matrix

structure DensityOperator (n : ℕ) where
  op : Matrix (Fin n) (Fin n) ℂ
  is_hermitian : op.IsHermitian
  is_trace_one : op.trace = 1

structure UnitaryOperator (n : ℕ) where
  op : Matrix (Fin n) (Fin n) ℂ
  is_unitary_right : op * star op = 1
  is_unitary_left : star op * op = 1

theorem trace_unitary_invariance {n : ℕ} (U : UnitaryOperator n) (ρ : DensityOperator n) :
    (U.op * ρ.op * star U.op).trace = ρ.op.trace := by
  have h : (U.op * ρ.op * star U.op).trace = (ρ.op * (star U.op * U.op)).trace := by
    rw [← Matrix.trace_mul_comm, mul_assoc]
  rw [h, U.is_unitary_left, mul_one]

theorem hermitian_preserved {n : ℕ} (U : UnitaryOperator n) (ρ : DensityOperator n) :
    (U.op * ρ.op * star U.op).IsHermitian :=
  ρ.is_hermitian.unitaryConj U.op

structure CertifiedKernel (n : ℕ) where
  trace_invariant : ∀ (U : UnitaryOperator n) (ρ : DensityOperator n),
    (U.op * ρ.op * star U.op).trace = ρ.op.trace
  hermitian_preservation : ∀ (U : UnitaryOperator n) (ρ : DensityOperator n),
    (U.op * ρ.op * star U.op).IsHermitian

def certify (n : ℕ) : CertifiedKernel n where
  trace_invariant := trace_unitary_invariance
  hermitian_preservation := hermitian_preserved

end Matrix7
