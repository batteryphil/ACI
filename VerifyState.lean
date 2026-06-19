import Mathlib

namespace ACI.VerifyState

theorem contraction_mapping_verified
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (T : α → α) (k : ℝ) (hk : k < 1) (hk0 : 0 ≤ k)
    (hT : ∀ x y, dist (T x) (T y) ≤ k * dist x y) :
    ∃ x : α, T x = x := by
  have hk' : (⟨k, hk0⟩ : NNReal) < 1 := by exact_mod_cast hk
  have hLip : LipschitzWith (⟨k, hk0⟩ : NNReal) T := by
    intro x y; simp only [NNReal.coe_mk]; exact hT x y
  have hContr : ContractingWith (⟨k, hk0⟩ : NNReal) T := ⟨hk', hLip⟩
  exact ⟨hContr.fixedPoint, hContr.fixedPoint_isFixedPt⟩

theorem banach_fixed_point_verified
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (T : α → α) (k : ℝ) (hk : k < 1) (hk0 : 0 ≤ k)
    (hT : ∀ x y, dist (T x) (T y) ≤ k * dist x y) :
    ∃ x : α, T x = x :=
  contraction_mapping_verified T k hk hk0 hT

def bridge_status : String := "LEAN_VERIFIED:OBLIGATIONS_SATISFIED"

end ACI.VerifyState
