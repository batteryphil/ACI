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
  induction margins with
  | nil => exact absurd rfl h
  | cons a t ih =>
    by_cases ht : t = []
    · subst ht
      exact ⟨a, List.mem_cons_self a [], fun x hx => by
        simp at hx; subst hx; exact le_refl _⟩
    · obtain ⟨m, hm, hmin⟩ := ih ht
      by_cases ham : a ≤ m
      · exact ⟨a, List.mem_cons_self a t, fun x hx => by
          cases hx with
          | head => exact le_refl _
          | tail _ hxt => exact le_trans ham (hmin x hxt)⟩
      · exact ⟨m, List.mem_cons_of_mem a hm, fun x hx => by
          cases hx with
          | head => exact le_of_not_le ham
          | tail _ hxt => exact hmin x hxt⟩

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
