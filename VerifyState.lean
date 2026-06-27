import Mathlib

namespace ACI.VerifyState

theorem contraction_mapping_verified
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (T : α → α) (k : ℝ) (hk : k < 1) (hk0 : 0 ≤ k)
    (hT : ∀ x y, dist (T x) (T y) ≤ k * dist x y) :
    ∃ x : α, T x = x := by
  let k' : NNReal := ⟨k, hk0⟩
  have hk' : k' < 1 := by exact_mod_cast hk
  have hLip : LipschitzWith k' T :=
    lipschitzWith_iff_dist_le_mul.mpr (fun x y => by exact_mod_cast hT x y)
  have hContr : ContractingWith k' T := ⟨hk', hLip⟩
  exact ⟨hContr.fixedPoint, hContr.fixedPoint_isFixedPt⟩

theorem banach_fixed_point_verified
    {α : Type*} [MetricSpace α] [CompleteSpace α] [Nonempty α]
    (T : α → α) (k : ℝ) (hk : k < 1) (hk0 : 0 ≤ k)
    (hT : ∀ x y, dist (T x) (T y) ≤ k * dist x y) :
    ∃ x : α, T x = x :=
  contraction_mapping_verified T k hk hk0 hT

def bridge_status : String := "LEAN_VERIFIED:OBLIGATIONS_SATISFIED"

end ACI.VerifyState
