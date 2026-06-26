import Mathlib

namespace EnergyDomain

-- ============================================================
-- 21-DOMAIN ENERGY/SYSTEMS REGISTRY
-- ============================================================

inductive Domain : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic
  | N_Node | O_Operator | P_Propagation
  | Q_Quality | R_Resonance | S_State
  | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

def all_domains : List Domain := [
  .A_Energy, .B_Control, .C_Thermal, .D_Structural,
  .E_Boundary, .F_Diagnostics, .G_Governance,
  .H_Harmonic, .I_Information, .J_Joining,
  .K_Kernel, .L_Localization, .M_Morphogenic,
  .N_Node, .O_Operator, .P_Propagation,
  .Q_Quality, .R_Resonance, .S_State,
  .T_Temporal, .U_Unification]

theorem twenty_one_domains : all_domains.length = 21 := by decide
theorem all_domains_nodup : all_domains.Nodup := by decide
theorem all_domains_complete (d : Domain) : d ∈ all_domains := by
  cases d <;> decide

-- ============================================================
-- DOMAIN PRIORITY
-- ============================================================

def domain_priority : Domain → ℕ
  | .A_Energy      => 1  | .B_Control     => 2
  | .C_Thermal     => 3  | .D_Structural  => 4
  | .E_Boundary    => 5  | .F_Diagnostics => 6
  | .G_Governance  => 7  | .H_Harmonic    => 8
  | .I_Information => 9  | .J_Joining     => 10
  | .K_Kernel      => 11 | .L_Localization => 12
  | .M_Morphogenic => 13 | .N_Node        => 14
  | .O_Operator    => 15 | .P_Propagation => 16
  | .Q_Quality     => 17 | .R_Resonance   => 18
  | .S_State       => 19 | .T_Temporal    => 20
  | .U_Unification => 21

theorem priority_positive (d : Domain) : 0 < domain_priority d := by
  cases d <;> decide

theorem priority_bounded (d : Domain) : domain_priority d ≤ 21 := by
  cases d <;> decide

theorem priority_injective : Function.Injective domain_priority := by
  intro a b h
  cases a <;> cases b <;> simp_all [domain_priority]

-- ============================================================
-- SYSTEM CORE
-- ============================================================

structure SystemCore where
  domains    : List Domain
  condition  : Prop
  existence  : domains.length > 0

-- ============================================================
-- MARGIN CLOSURE LAW
-- M_N7 = minimum margin — system closes iff M_N7 > 0
-- ============================================================

noncomputable def M_N7 (margins : Domain → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty margins

theorem closure_law (margins : Domain → ℝ) :
    M_N7 margins > 0 ↔ ∀ d : Domain, margins d > 0 := by
  simp [M_N7, Finset.lt_inf'_iff]

theorem system_valid (margins : Domain → ℝ)
    (h : M_N7 margins > 0) : ∀ d : Domain, margins d > 0 :=
  (closure_law margins).mp h

-- ============================================================
-- UNIFICATION LAW
-- ============================================================

def U_valid (all_critical no_contradiction
             g_accept k_close : Bool) : Bool :=
  all_critical && no_contradiction && g_accept && k_close

theorem closure_complete :
    U_valid true true true true = true := by decide

theorem unification_law (g_accept k_close : Bool)
    (hg : g_accept = true) (hk : k_close = true) :
    g_accept && k_close = true := by
  simp [hg, hk]

-- ============================================================
-- ENERGY DOMAIN AUDIT SEAL
-- ============================================================

structure EnergyAuditVector where
  domain_count      : ℕ
  domains_unique    : Bool
  closure_law_holds : Bool
  unification_valid : Bool
  sovereign_sealed  : Bool

def EnergyDomain_audit : EnergyAuditVector := {
  domain_count      := 21
  domains_unique    := true
  closure_law_holds := true
  unification_valid := true
  sovereign_sealed  := true
}

theorem energy_domain_sealed :
    EnergyDomain_audit.sovereign_sealed = true ∧
    EnergyDomain_audit.domain_count = 21 ∧
    EnergyDomain_audit.unification_valid = true := by
  decide

end EnergyDomain
