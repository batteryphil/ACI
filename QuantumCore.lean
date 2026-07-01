import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# QUANTUMCORE: ACI SOVEREIGN QUANTUM OPERATOR ENGINE
-/

open Complex

namespace QuantumCore

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H] [Nontrivial H]

structure DensityOperator where
  op      : H →L[ℂ] H
  h_sa    : ContinuousLinearMap.adjoint op = op
  h_pos   : ∀ v : H, 0 ≤ (inner (𝕜 := ℂ) v (op v)).re
  h_trace : (LinearMap.trace ℂ H (op : H →ₗ[ℂ] H)).re = 1

theorem density_trace_one (ρ : DensityOperator) :
    (LinearMap.trace ℂ H (ρ.op : H →ₗ[ℂ] H)).re = 1 := ρ.h_trace

theorem sa_real_diagonal (A : H →L[ℂ] H)
    (hA : ContinuousLinearMap.adjoint A = A) (v : H) :
    (inner (𝕜 := ℂ) v (A v)).im = 0 := by
  have step1 : inner (𝕜 := ℂ) (A v) v = inner (𝕜 := ℂ) v (A v) := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hA]
  have step2 : inner (𝕜 := ℂ) (A v) v = starRingEnd ℂ (inner (𝕜 := ℂ) v (A v)) :=
    inner_conj_symm v (A v)
  rw [← step1, step2]
  exact Complex.im_eq_zero_of_conj_eq rfl

theorem sa_real_linear (A B : H →L[ℂ] H) (α β : ℝ)
    (hA : ContinuousLinearMap.adjoint A = A) (hB : ContinuousLinearMap.adjoint B = B) :
    ContinuousLinearMap.adjoint ((α : ℂ) • A + (β : ℂ) • B) = (α : ℂ) • A + (β : ℂ) • B := by
  simp [ContinuousLinearMap.adjoint_add, ContinuousLinearMap.adjoint_smul, hA, hB]

theorem sa_composition_seal (ρ P : H →L[ℂ] H)
    (hρ : ContinuousLinearMap.adjoint ρ = ρ) (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (P.comp (ρ.comp P)) = P.comp (ρ.comp P) := by
  simp [ContinuousLinearMap.adjoint_comp, hP, hρ]

theorem sa_trace_real (A : H →L[ℂ] H) (hA : ContinuousLinearMap.adjoint A = A) :
    (LinearMap.trace ℂ H (A : H →ₗ[ℂ] H)).im = 0 := by
  have h := LinearMap.trace_conj ℂ H (A : H →ₗ[ℂ] H)
  rw [← ContinuousLinearMap.coe_toLinearMap_adjoint, hA] at h
  exact Complex.im_eq_zero_of_conj_eq h

structure Projector where
  op   : H →L[ℂ] H
  h_sa : ContinuousLinearMap.adjoint op = op
  h_id : op.comp op = op

theorem proj_idempotent (P : Projector) (v : H) : P.op (P.op v) = P.op v :=
  ContinuousLinearMap.ext_iff.mp P.h_id v

theorem proj_spectrum (P : Projector) (v : H) (lam : ℂ)
    (hv : P.op v = lam • v) (hv_ne : v ≠ 0) :
    lam = 0 ∨ lam = 1 := by
  have h1 : P.op (P.op v) = P.op v := proj_idempotent P v
  rw [hv, ContinuousLinearMap.map_smul, hv, smul_smul] at h1
  rw [← sub_eq_zero] at h1
  rw [← sub_smul] at h1
  exact smul_eq_zero.mp h1 |>.resolve_right (ne_zero_of_ne hv_ne) |> Or.symm

noncomputable def meas_prob (ρ : DensityOperator) (P : Projector) : ℝ :=
  (LinearMap.trace ℂ H ((ρ.op.comp P.op) : H →ₗ[ℂ] H)).re

theorem meas_prob_cyclic (ρ : DensityOperator) (P : Projector) :
    meas_prob ρ P = (LinearMap.trace ℂ H ((P.op.comp (ρ.op.comp P.op)) : H →ₗ[ℂ] H)).re := by
  unfold meas_prob
  congr 1
  exact (LinearMap.trace_mul_comm ℂ (ρ.op : H →ₗ[ℂ] H) (P.op : H →ₗ[ℂ] H)).symm

noncomputable def post_meas_op (ρ : DensityOperator) (P : Projector)
    (h_prob : 0 < meas_prob ρ P) : H →L[ℂ] H :=
  (1 / (meas_prob ρ P : ℂ)) • (P.op.comp (ρ.op.comp P.op))

theorem post_meas_sa (ρ : DensityOperator) (P : Projector) (h_prob : 0 < meas_prob ρ P) :
    ContinuousLinearMap.adjoint (post_meas_op ρ P h_prob) = post_meas_op ρ P h_prob := by
  unfold post_meas_op
  simp [ContinuousLinearMap.adjoint_smul, sa_composition_seal ρ.op P.op ρ.h_sa P.h_sa]

structure UnitaryOp where
  op    : H →L[ℂ] H
  h_adj : (ContinuousLinearMap.adjoint op).comp op = ContinuousLinearMap.id ℂ H
  h_inv : op.comp (ContinuousLinearMap.adjoint op) = ContinuousLinearMap.id ℂ H

theorem unitary_trace_invariant (U : UnitaryOp) (A : H →L[ℂ] H) :
    LinearMap.trace ℂ H ((U.op.comp A.comp (ContinuousLinearMap.adjoint U.op)) : H →ₗ[ℂ] H)
    = LinearMap.trace ℂ H (A : H →ₗ[ℂ] H) := by
  rw [LinearMap.trace_mul_comm (U.op : H →ₗ[ℂ] H)]
  simp [ContinuousLinearMap.coe_comp, ContinuousLinearMap.adjoint_comp, U.h_inv]

def is_pure_state (ρ : DensityOperator) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ∀ v : H, ρ.op v = inner (𝕜 := ℂ) ψ v • ψ

theorem pure_state_idempotent (ρ : DensityOperator) (hpure : is_pure_state ρ) (v : H) :
    ρ.op (ρ.op v) = ρ.op v := by
  obtain ⟨ψ, hψ_norm, hψ⟩ := hpure
  simp [hψ, inner_smul_right, hψ_norm]

end QuantumCore

