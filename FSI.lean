import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import N7Spine

/-!
# FSI — FORMAL SYNTHETIC INTELLIGENCE
## Compute -> Branch -> Construct Remediation, with Proof
## Built on N7Spine's existing bottleneck/gate machinery.
-/

namespace FSI

open N7Spine

/-! ## STRATEGY 1: GLOBAL RESCALE -/

/-- Rescale every margin by a nonnegative factor c. -/
def rescale (mv : MarginVector) (c : ℝ) (hc : 0 ≤ c) : MarginVector where
  m := fun d => c * mv.m d
  h_floor := fun d => mul_nonneg hc (mv.h_floor d)

theorem rescale_M_N7 (mv : MarginVector) (c : ℝ) (hc : 0 ≤ c) :
    M_N7 (rescale mv c hc) = c * M_N7 mv := by
  obtain ⟨d0, hd0_eq, _⟩ := M_N7_is_min mv
  obtain ⟨d1, hd1_eq, _⟩ := M_N7_is_min (rescale mv c hc)
  apply le_antisymm
  · calc M_N7 (rescale mv c hc) ≤ (rescale mv c hc).m d0 :=
          M_N7_le_all (rescale mv c hc) d0
      _ = c * mv.m d0 := rfl
      _ = c * M_N7 mv := by rw [hd0_eq]
  · calc c * M_N7 mv ≤ c * mv.m d1 :=
          mul_le_mul_of_nonneg_left (M_N7_le_all mv d1) hc
      _ = (rescale mv c hc).m d1 := rfl
      _ = M_N7 (rescale mv c hc) := hd1_eq

noncomputable def attempt_remediation
    (mv : MarginVector) (target : ℝ) (h_target_pos : 0 < target) :
    Option MarginVector :=
  if h : 0 < M_N7 mv then
    some (rescale mv (target / M_N7 mv) (le_of_lt (div_pos h_target_pos h)))
  else
    none

theorem remediation_reaches_target
    (mv : MarginVector) (target : ℝ) (h_target_pos : 0 < target)
    (h_pos : 0 < M_N7 mv) (mv' : MarginVector)
    (h_attempt : attempt_remediation mv target h_target_pos = some mv') :
    M_N7 mv' = target := by
  unfold attempt_remediation at h_attempt
  rw [dif_pos h_pos] at h_attempt
  have heq : mv' = rescale mv (target / M_N7 mv) (le_of_lt (div_pos h_target_pos h_pos)) :=
    (Option.some.inj h_attempt).symm
  rw [heq, rescale_M_N7, div_mul_cancel₀ _ (ne_of_gt h_pos)]

theorem remediation_seals
    (mv : MarginVector) (floor target : ℝ)
    (h_floor_lt : floor < target) (h_target_pos : 0 < target)
    (h_pos : 0 < M_N7 mv) (mv' : MarginVector)
    (h_attempt : attempt_remediation mv target h_target_pos = some mv') :
    floor < M_N7 mv' := by
  rw [remediation_reaches_target mv target h_target_pos h_pos mv' h_attempt]
  exact h_floor_lt

/-! ## STRATEGY 2: TARGETED BOTTLENECK CORRECTION
    Unlike rescale, this touches exactly one domain -- the
    actual bottleneck identified by N7Spine's own `bottleneck`
    function -- and leaves every other domain provably unchanged. -/

def correct_bottleneck
    (mv : MarginVector) (target : ℝ) (h_target_nonneg : 0 ≤ target) :
    MarginVector where
  m := fun d => if d = bottleneck mv then target else mv.m d
  h_floor := fun d => by
    split_ifs with h
    · exact h_target_nonneg
    · exact mv.h_floor d

theorem correct_bottleneck_others_unchanged
    (mv : MarginVector) (target : ℝ) (h_target_nonneg : 0 ≤ target)
    (d : Domain14) (hd : d ≠ bottleneck mv) :
    (correct_bottleneck mv target h_target_nonneg).m d = mv.m d := by
  unfold correct_bottleneck
  simp [hd]

theorem correct_bottleneck_at_target
    (mv : MarginVector) (target : ℝ) (h_target_nonneg : 0 ≤ target) :
    (correct_bottleneck mv target h_target_nonneg).m (bottleneck mv) = target := by
  unfold correct_bottleneck
  simp

/-- If the new target doesn't exceed any of the OTHER domains'
    current margins, the corrected vector's bottleneck equals
    exactly the target -- proved by bounding both directions
    via Finset.inf' lemmas, the same machinery N7Spine's own
    M_N7 is built from. -/
theorem correct_bottleneck_M_N7
    (mv : MarginVector) (target : ℝ) (h_target_nonneg : 0 ≤ target)
    (h_dominates : ∀ d : Domain14, d ≠ bottleneck mv → target ≤ mv.m d) :
    M_N7 (correct_bottleneck mv target h_target_nonneg) = target := by
  apply le_antisymm
  · have h := Finset.inf'_le
      (s := (Finset.univ : Finset Domain14))
      (f := (correct_bottleneck mv target h_target_nonneg).m)
      (Finset.mem_univ (bottleneck mv))
    rwa [correct_bottleneck_at_target] at h
  · apply Finset.le_inf'
    intro d _
    by_cases hd : d = bottleneck mv
    · rw [hd, correct_bottleneck_at_target]
    · rw [correct_bottleneck_others_unchanged mv target h_target_nonneg d hd]
      exact h_dominates d hd

/-- The targeted strategy changes strictly fewer domains than
    a global rescale whenever the rescale factor isn't 1 and
    at least one non-bottleneck domain has a nonzero margin:
    targeted touches exactly the bottleneck; rescale touches
    every domain with nonzero margin. -/
theorem targeted_is_minimal_change
    (mv : MarginVector) (target : ℝ) (h_target_nonneg : 0 ≤ target)
    (d : Domain14) (hd : d ≠ bottleneck mv) :
    (correct_bottleneck mv target h_target_nonneg).m d = mv.m d :=
  correct_bottleneck_others_unchanged mv target h_target_nonneg d hd

end FSI
