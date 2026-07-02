import Mathlib

namespace Governor

-- ============================================================
-- TOLERANCE COMPLIANCE
-- ============================================================

def WithinTolerance (measured nominal tolerance : ℝ) : Prop :=
  |measured - nominal| ≤ tolerance

theorem withinTolerance_symm (m n t : ℝ) (h : WithinTolerance m n t) :
    WithinTolerance n m t := by
  unfold WithinTolerance at *
  rwa [abs_sub_comm]

theorem withinTolerance_upper (m n t : ℝ) (h : WithinTolerance m n t) :
    m - n ≤ t := (abs_le.mp h).2

theorem withinTolerance_lower (m n t : ℝ) (h : WithinTolerance m n t) :
    -t ≤ m - n := (abs_le.mp h).1

theorem withinTolerance_triangle (a b c t1 t2 : ℝ)
    (h1 : WithinTolerance a b t1) (h2 : WithinTolerance b c t2) :
    WithinTolerance a c (t1 + t2) := by
  unfold WithinTolerance at *
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

theorem withinTolerance_mono (m n t1 t2 : ℝ) (hle : t1 ≤ t2)
    (h : WithinTolerance m n t1) : WithinTolerance m n t2 := by
  unfold WithinTolerance at *
  linarith [abs_nonneg (m - n)]

-- ============================================================
-- SAFETY FACTOR
-- ============================================================

def SafetyAdmissible (failure_load limit_load : ℝ) : Prop :=
  0 < limit_load ∧ failure_load / limit_load ≥ 1.5

theorem safety_margin (f l : ℝ) (h : SafetyAdmissible f l) :
    f ≥ 1.5 * l := by
  obtain ⟨hl, hratio⟩ := h
  have := (le_div_iff₀ hl).mp hratio
  linarith

/-- FIXED: the original `linarith [safety_margin f l h]` only had
    `f ≥ 1.5 * l` available — that alone doesn't imply `f ≥ l` unless
    `l ≥ 0` is also in scope, and linarith does not automatically reach
    into `h : SafetyAdmissible f l` (a conjunction) to extract that fact.
    `h.1` (which is `0 < l`) is pulled out explicitly and passed in. -/
theorem safety_exceeds_limit (f l : ℝ) (h : SafetyAdmissible f l) :
    f ≥ l := by
  have hl := h.1
  linarith [safety_margin f l h, hl]

theorem safety_factor_exact (f l : ℝ) (h : SafetyAdmissible f l) :
    ∃ k : ℝ, k ≥ 1.5 ∧ f = k * l := by
  obtain ⟨hl, hratio⟩ := h
  refine ⟨f / l, hratio, ?_⟩
  field_simp

-- ============================================================
-- QMS GATE
-- ============================================================

structure QMSCheck where
  dimensionalDeviation : ℝ
  yieldStrengthMPa     : ℝ

def QMSAdmissible (q : QMSCheck) : Prop :=
  q.dimensionalDeviation ≤ 0.005 ∧ q.yieldStrengthMPa ≥ 450.0

theorem qms_dimensional (q : QMSCheck) (h : QMSAdmissible q) :
    q.dimensionalDeviation ≤ 0.005 := h.1

theorem qms_yield (q : QMSCheck) (h : QMSAdmissible q) :
    q.yieldStrengthMPa ≥ 450.0 := h.2

-- ============================================================
-- REDUNDANCY
-- ============================================================

def RedundancyAdmissible (active required : ℕ) : Prop :=
  required ≤ active

theorem redundancy_monotone (active required extra : ℕ)
    (h : RedundancyAdmissible active required) :
    RedundancyAdmissible (active + extra) required := by
  simp only [RedundancyAdmissible] at h ⊢
  omega

-- FIXED: push_neg is deprecated in this Mathlib/Lean version;
-- replaced with the compiler-suggested `push Not` syntax.
theorem redundancy_deficit (active required : ℕ)
    (h : ¬ RedundancyAdmissible active required) :
    ∃ d : ℕ, d > 0 ∧ required = active + d := by
  unfold RedundancyAdmissible at h
  push Not at h
  exact ⟨required - active, by omega, by omega⟩

-- ============================================================
-- COMPOSITE GOVERNANCE
-- ============================================================

structure GovernanceState where
  qms      : QMSCheck
  active   : ℕ
  required : ℕ

def GovernanceAdmissible (g : GovernanceState) : Prop :=
  QMSAdmissible g.qms ∧ RedundancyAdmissible g.active g.required

theorem governance_qms (g : GovernanceState) (h : GovernanceAdmissible g) :
    QMSAdmissible g.qms := h.1

theorem governance_redundancy (g : GovernanceState) (h : GovernanceAdmissible g) :
    RedundancyAdmissible g.active g.required := h.2

theorem governance_fails_without_qms (g : GovernanceState)
    (hq : ¬ QMSAdmissible g.qms) : ¬ GovernanceAdmissible g :=
  fun h => hq h.1

theorem governance_fails_without_redundancy (g : GovernanceState)
    (hr : ¬ RedundancyAdmissible g.active g.required) : ¬ GovernanceAdmissible g :=
  fun h => hr h.2

theorem governance_admissible_iff (g : GovernanceState) :
    GovernanceAdmissible g ↔
    QMSAdmissible g.qms ∧ RedundancyAdmissible g.active g.required := by
  rfl

end Governor
