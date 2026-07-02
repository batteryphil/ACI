import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

open Complex
open scoped BigOperators

variable {H : Type*}
variable [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]
variable [CompleteSpace H]
variable [Nontrivial H]

/- =========================
   Core Structures
========================= -/

structure DensityOperator where
  op : H →L[ℂ] H

structure Projector where
  op : H →L[ℂ] H
  idempotent : op ∘ₗ op = op

structure UnitaryOp where
  op : H →L[ℂ] H
  adjoint_mul :
    (ContinuousLinearMap.adjoint op) ∘ₗ op = LinearMap.id

/-- Promote LinearMap composition to ContinuousLinearMap composition -/
def compSL (A B : H →L[ℂ] H) : H →L[ℂ] H :=
  A ∘ₗ B

infixr:80 " ∘ₛₗ " => compSL

/-- Trace shorthand -/
def Tr (A : H →L[ℂ] H) : ℂ :=
  LinearMap.trace ℂ H A

/- =========================
   Core Theorems
========================= -/

/-- Cyclic property of trace (2-term) -/
theorem trace_cyclic (A B : H →L[ℂ] H) :
    Tr (A ∘ₛₗ B) = Tr (B ∘ₛₗ A) :=
by
  simpa [Tr, compSL] using LinearMap.trace_comp_comm A B

/-- Cyclic property (3-term rotation) -/
theorem trace_cyclic_three (A B C : H →L[ℂ] H) :
    Tr (A ∘ₛₗ B ∘ₛₗ C) = Tr (B ∘ₛₗ C ∘ₛₗ A) :=
by
  simpa [Tr, compSL]
    using LinearMap.trace_comp_comm (A ∘ₗ B) C

/-- Projector sandwich identity -/
theorem trace_projector_sandwich
  (ρ : DensityOperator) (P : Projector) :
  Tr (ρ.op ∘ₛₗ P.op)
    = Tr (P.op ∘ₛₗ ρ.op ∘ₛₗ P.op) :=
by
  classical

  -- Step 1: cyclic swap
  have h₁ :
    Tr (ρ.op ∘ₛₗ P.op)
      = Tr (P.op ∘ₛₗ ρ.op) :=
    trace_cyclic _ _

  -- Step 2: use idempotence
  have h₂ : P.op ∘ₛₗ P.op = P.op := by
    simpa [compSL] using P.idempotent

  -- Step 3: rebuild safely
  calc
    Tr (ρ.op ∘ₛₗ P.op)
        = Tr (P.op ∘ₛₗ ρ.op) := h₁
    _ = Tr ((P.op ∘ₛₗ ρ.op) ∘ₛₗ P.op) := by
        simp [h₂]
    _ = Tr (P.op ∘ₛₗ ρ.op ∘ₛₗ P.op) := rfl

/-- Unitary invariance of trace -/
theorem trace_unitary_invariant
  (U : UnitaryOp) (A : H →L[ℂ] H) :
  Tr (U.op ∘ₛₗ A ∘ₛₗ ContinuousLinearMap.adjoint U.op)
    = Tr A :=
by
  classical

  -- Step 1: rotate trace
  have h₁ :
    Tr (U.op ∘ₛₗ A ∘ₛₗ ContinuousLinearMap.adjoint U.op)
      = Tr (A ∘ₛₗ ContinuousLinearMap.adjoint U.op ∘ₛₗ U.op) :=
    trace_cyclic_three _ _ _

  -- Step 2: collapse adjoint * U = I
  have h₂ :
    ContinuousLinearMap.adjoint U.op ∘ₛₗ U.op = LinearMap.id := by
    simpa [compSL] using U.adjoint_mul

  -- Step 3: finalize
  simpa [h₂, compSL] using h₁

/- =========================
   Inner Product Layer
========================= -/

/-- Basic projector action (definition-level) -/
theorem projector_action (ψ v : H) :
  (inner ℂ ψ v • ψ) = ((inner ℂ ψ v) • ψ) :=
rfl

/-- Inner expansion identity -/
theorem projector_inner_expand (ψ v : H) :
  inner ℂ ψ (inner ℂ ψ v • ψ)
    = inner ℂ ψ v * ‖ψ‖ ^ 2 :=
by
  simpa using inner_smul_right ψ ψ (inner ℂ ψ v)

/-- Lift scalar identity to vector form -/
theorem projector_vector_form (ψ v : H) :
  inner ℂ ψ (inner ℂ ψ v • ψ) • ψ
    = (inner ℂ ψ v * ‖ψ‖ ^ 2) • ψ :=
by
  have h :=
    inner_smul_right ψ ψ (inner ℂ ψ v)
  simpa using congrArg (fun x => x • ψ) h

/- =========================
   Probability Interpretation
========================= -/

/-- Measurement probability (Born rule form) -/
def measurementProb (ρ : DensityOperator) (P : Projector) : ℂ :=
  Tr (ρ.op ∘ₛₗ P.op)

/-- Stability under projector sandwich -/
theorem measurement_stable
  (ρ : DensityOperator) (P : Projector) :
  measurementProb ρ P
    = Tr (P.op ∘ₛₗ ρ.op ∘ₛₗ P.op) :=
by
  simpa [measurementProb]
    using trace_projector_sandwich ρ P

/- =========================
   End QuantumCore
========================= -/
