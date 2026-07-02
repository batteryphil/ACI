import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.NormedSpace.ContinuousLinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Complex.Basic

noncomputable section
open Complex
open scoped BigOperators

namespace quantum core

section Core

variable {H : Type*}
variable [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]
variable [CompleteSpace H]
variable [Nontrivial H]

abbrev CLO := ContinuousLinearMap ℂ H H

structure DensityOperator where
  op            : CLO
  pos           : ∀ x, 0 ≤ realPart ⟪x, op x⟫
  trace_one     : LinearMap.trace ℂ H op.toLinearMap = 1
  self_adjoint  : op.adjoint = op

structure Projector where
  op        : CLO
  idempotent : op.comp op = op
  self_adj   : op.adjoint = op

structure UnitaryOp where
  op : CLO
  unitary :
    op.adjoint.comp op = ContinuousLinearMap.id ℂ H ∧
    op.comp op.adjoint = ContinuousLinearMap.id ℂ H

def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H (ρ.op.comp P.op).toLinearMap).re

theorem meas_prob_nonneg (ρ : DensityOperator) (P : Projector) :
  0 ≤ meas_prob ρ P := by
  unfold meas_prob
  have := LinearMap.trace_nonneg_of_pos
    (T := (ρ.op.comp P.op).toLinearMap)
    (by
      intro x
      have := ρ.pos (P.op x)
      simpa using this)
  simpa using this

theorem meas_prob_cyclic (ρ : DensityOperator) (P : Projector) :
  meas_prob ρ P =
    (LinearMap.trace ℂ H (P.op.comp (ρ.op.comp P.op)).toLinearMap).re := by
  unfold meas_prob
  have h1 :
    (ρ.op.comp P.op).toLinearMap =
    ρ.op.toLinearMap.comp P.op.toLinearMap := rfl

  have h2 :
    (P.op.comp (ρ.op.comp P.op)).toLinearMap =
    P.op.toLinearMap.comp (ρ.op.toLinearMap.comp P.op.toLinearMap) := rfl

  calc
    (LinearMap.trace ℂ H (ρ.op.comp P.op).toLinearMap).re
        = (LinearMap.trace ℂ H (ρ.op.toLinearMap.comp P.op.toLinearMap)).re := by
            rw [h1]
    _ = (LinearMap.trace ℂ H (P.op.toLinearMap.comp ρ.op.toLinearMap)).re := by
            rw [LinearMap.trace_mul_comm]
    _ = (LinearMap.trace ℂ H
          (P.op.toLinearMap.comp (ρ.op.toLinearMap.comp P.op.toLinearMap))).re := by
            rw [← LinearMap.comp_assoc]
    _ = (LinearMap.trace ℂ H
          (P.op.comp (ρ.op.comp P.op)).toLinearMap).re := by
            rw [h2]

def evolve (ρ : DensityOperator) (U : UnitaryOp) : DensityOperator :=
{
  op := U.op.comp ρ.op.comp U.op.adjoint,
  pos := by
    intro x
    have := ρ.pos (U.op.adjoint x)
    simpa using this,
  trace_one := by
    have h := LinearMap.trace_conj
      (f := U.op.toLinearMap)
      (g := ρ.op.toLinearMap)
    simpa using h,
  self_adjoint := by
    ext x
    simp [ContinuousLinearMap.adjoint_comp]
}

structure QuantumAuditVector where
  trace_ok      : Bool
  positivity_ok : Bool
  adjoint_ok    : Bool

def audit (ρ : DensityOperator) : QuantumAuditVector :=
{
  trace_ok := (LinearMap.trace ℂ H ρ.op.toLinearMap == 1),
  positivity_ok := true,
  adjoint_ok := (ρ.op.adjoint == ρ.op)
}

end Core

section TangentSpace

variable {H : Type*}
variable [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]
variable [CompleteSpace H]
variable [Nontrivial H]

abbrev CLO := ContinuousLinearMap ℂ H H

def system_map
  (α β γ : CLO)
  (A : CLO)
  (T : CLO)
  (x : H) : H :=
  let update :=
    α x + β (A x) + γ (T x)
  update

def jacobian_vec
  (F : H → H)
  (x v : H)
  (ε : ℝ) : H :=
  (F (x + ε • v) - F x) / ε

def lyapunov_step
  (F : H → H)
  (x : H)
  (Q : Matrix (Fin (FiniteDimensional.finrank ℂ H))
              (Fin (FiniteDimensional.finrank ℂ H)) ℝ)
  : Matrix _ _ ℝ × Matrix _ _ ℝ :=
  let Z := Q
  let QR := Matrix.qr Z
  QR

end TangentSpace

end AWMQuantum
