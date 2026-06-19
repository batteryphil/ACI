import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace MoruzinLaw

structure SystemPresence where
  X     : Type
  D     : Type
  C     : Prop
  hX    : Nonempty X
  hD    : Nonempty D
  joint : C

theorem law_of_presence (s : SystemPresence) : s.C := s.joint

theorem absence_collapses_identity
    (C : Prop) (hC : Not C) :
    Not (Exists (fun s : SystemPresence => s.C = C)) := by
  intro h
  obtain ⟨s, hs⟩ := h
  exact hC (hs ▸ s.joint)

def chamber_valid (delta m_eff : Real) : Prop := |delta| <= m_eff

theorem breach_implies_halt (delta m_eff : Real)
    (hbreach : m_eff < |delta|) :
    Not (chamber_valid delta m_eff) := by
  simp [chamber_valid]; linarith

theorem chamber_composition (d1 d2 m1 m2 : Real)
    (h1 : chamber_valid d1 m1)
    (h2 : chamber_valid d2 m2) :
    chamber_valid (d1 + d2) (m1 + m2) := by
  simp [chamber_valid]
  calc |d1 + d2| <= |d1| + |d2| := abs_add d1 d2
    _ <= m1 + m2 := add_le_add h1 h2

theorem zero_always_valid (m : Real) (hm : 0 <= m) :
    chamber_valid 0 m := by simp [chamber_valid, hm]

structure UnificationState where
  all_domains_valid : Bool
  g_accept          : Bool
  k_close           : Bool

def unification_valid (u : UnificationState) : Bool :=
  u.all_domains_valid && u.g_accept && u.k_close

theorem unification_law (u : UnificationState)
    (hd : u.all_domains_valid = true)
    (hg : u.g_accept = true)
    (hk : u.k_close = true) :
    unification_valid u = true := by
  simp [unification_valid, hd, hg, hk]

theorem unification_fixed_point (u : UnificationState)
    (h : unification_valid u = true) :
    u.all_domains_valid = true /\ u.g_accept = true /\ u.k_close = true := by
  simp [unification_valid] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem contradiction_excluded (u : UnificationState)
    (h : unification_valid u = true) :
    Not (u.g_accept = false) := by
  have := (unification_fixed_point u h).2.1
  simp [this]

theorem domain_failure_breaks_unification (u : UnificationState)
    (hd : u.all_domains_valid = false) :
    unification_valid u = false := by
  simp [unification_valid, hd]

structure TerminalSeal where
  presence  : SystemPresence
  m_eff     : Real
  hm_pos    : 0 < m_eff
  unified   : UnificationState
  is_sealed : unification_valid unified = true

theorem terminal_seal_valid (seal : TerminalSeal) :
    unification_valid seal.unified = true := seal.is_sealed

theorem terminal_seal_presence (seal : TerminalSeal) : seal.presence.C :=
  seal.presence.joint

theorem terminal_seal_chamber (seal : TerminalSeal) :
    chamber_valid 0 seal.m_eff :=
  zero_always_valid seal.m_eff (le_of_lt seal.hm_pos)

theorem terminal_seal_uncontradicted (seal : TerminalSeal) :
    Not (seal.unified.g_accept = false) :=
  contradiction_excluded seal.unified seal.is_sealed

def AWM7_Seal : TerminalSeal where
  presence  := { X := Unit, D := Unit, C := True, hX := ⟨()⟩, hD := ⟨()⟩, joint := trivial }
  m_eff     := 1
  hm_pos    := by norm_num
  unified   := { all_domains_valid := true, g_accept := true, k_close := true }
  is_sealed := by decide

theorem awm7_sovereign_locked :
    unification_valid AWM7_Seal.unified = true /\
    AWM7_Seal.presence.C /\
    0 < AWM7_Seal.m_eff :=
  ⟨by decide, trivial, by norm_num⟩

theorem awm7_apex_certified :
    Not (AWM7_Seal.unified.g_accept = false) /\
    Not (AWM7_Seal.unified.k_close = false) /\
    Not (AWM7_Seal.unified.all_domains_valid = false) := by
  decide

end MoruzinLaw
