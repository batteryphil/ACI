import Mathlib

namespace Governor

-- ============================================================
-- TOLERANCE COMPLIANCE
-- ============================================================

def WithinTolerance (measured nominal tolerance : ℝ) : Prop :=
  |measured - nominal| ≤ tolerance

theorem withinTolerance_symm (m n t : ℝ) (h : WithinTolerance m n t) :
    WithinTolerance n m t := by
  simp [WithinTolerance, abs_sub_comm] at *; exact h

theorem withinTolerance_upper (m n t : ℝ) (h : WithinTolerance m n t) :
    m - n ≤ t := (abs_le.mp h).2

theorem withinTolerance_lower (m n t : ℝ) (h : WithinTolerance m n t) :
    -t ≤ m - n := (abs_le.mp h).1

theorem withinTolerance_triangle (a b c t1 t2 : ℝ)
    (h1 : WithinTolerance a b t1) (h2 : WithinTolerance b c t2) :
    WithinTolerance a c (t1 + t2) := by
  simp only [WithinTolerance]
  calc |a - c| = |a - b + (b - c)| := by ring_nf
    _ ≤ |a - b| + |b - c| := abs_add _ _
    _ ≤ t1 + t2 := add_le_add h1 h2

-- ============================================================
-- SAFETY FACTOR
-- ============================================================

def SafetyAdmissible (failure_load limit_load : ℝ) : Prop :=
  0 < limit_load ∧ failure_load / limit_load ≥ 1.5

theorem safety_margin (f l : ℝ) (h : SafetyAdmissible f l) :
    f ≥ 1.5 * l := by
  obtain ⟨hl, hratio⟩ := h
  rwa [ge_iff_le, ← div_le_iff hl]

theorem safety_exceeds_limit (f l : ℝ) (h : SafetyAdmissible f l) :
    f ≥ l := by linarith [safety_margin f l h]

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
  simp [RedundancyAdmissible]; omega

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

end Governor
