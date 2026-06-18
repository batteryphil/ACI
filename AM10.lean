import Mathlib.Tactic

namespace AM10

structure SystemCore where
  X : Type
  D : Type
  C : Prop
  existence : C

theorem system_exists (s : SystemCore) : s.C := s.existence

inductive NodeChain
  | N1 | N2 | N3 | N4 | N5 | N6 | N7
  deriving DecidableEq, Repr

def M_N7 (margins : List ℚ) : ℚ :=
  margins.foldl min 1

theorem validity_requires_positive_margin
    (margins : List ℚ) (h : 0 < M_N7 margins) :
    M_N7 margins > 0 := h

theorem bottleneck_law (margins : List ℚ)
    (h : margins ≠ []) :
    ∃ m ∈ margins, ∀ x ∈ margins, m ≤ x := by
  obtain ⟨m, hm, hmin⟩ := List.exists_min_image margins id h
  exact ⟨m, hm, fun x hx => hmin x hx⟩

theorem closure_gate (M_N7_val : ℚ)
    (h : M_N7_val > 0) : True := trivial

theorem halt_condition (M_N7_val : ℚ)
    (h : M_N7_val ≤ 0) : M_N7_val ≤ 0 := h

def SystemValid (margins : List ℚ) : Prop :=
  M_N7 margins > 0

theorem global_closure (margins : List ℚ)
    (h : SystemValid margins) :
    M_N7 margins > 0 := h

end AM10
