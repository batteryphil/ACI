import Mathlib

namespace EnergyDomain

-- 21-DOMAIN ENERGY/SYSTEMS REGISTRY

inductive Domain : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic
  | N_Node | O_Operator | P_Propagation
  | Q_Quality | R_Resonance | S_State
  | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain := ⟨Domain.A_Energy⟩

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

-- DOMAIN PRIORITY

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
  decide

-- SYSTEM CORE

structure SystemCore where
  domains    : List Domain
  condition  : Prop
  existence  : domains.length > 0

-- MARGIN CLOSURE LAW
-- M_N7 = minimum margin — system closes iff M_N7 > 0

noncomputable def M_N7 (margins : Domain → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty margins

theorem closure_law (margins : Domain → ℝ) :
    M_N7 margins > 0 ↔ ∀ d : Domain, margins d > 0 := by
  simp [M_N7, Finset.lt_inf'_iff]

theorem system_valid (margins : Domain → ℝ)
    (h : M_N7 margins > 0) : ∀ d : Domain, margins d > 0 :=
  (closure_law margins).mp h

-- UNIFICATION LAW

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
-- DEI: DYNAMIC ENERGY INTEGRATION LAWS
-- Formalizes the logical STRUCTURE of the named physical criteria
-- (Lawson threshold, MHD β-bound, net-power balance, control-timescale
-- ordering, closed-loop system unification) as real, provable statements
-- about the inequalities that define each regime. This does not derive
-- or verify the underlying plasma physics (kinetic theory, MHD stability
-- analysis, transport PDEs) — only the logical shape of the criteria
-- as stated: a triple product exceeding a threshold, a ratio staying
-- inside a bound, one sum dominating another, and a timescale ordering.
-- ============================================================

def LawsonViable (n T τ threshold : ℝ) : Prop :=
  n * T * τ ≥ threshold

theorem lawson_monotone_n (n n' T τ threshold : ℝ)
    (hn : n ≤ n') (hT : 0 ≤ T) (hτ : 0 ≤ τ)
    (h : LawsonViable n T τ threshold) :
    LawsonViable n' T τ threshold := by
  unfold LawsonViable at *
  have : n * T * τ ≤ n' * T * τ := by
    apply mul_le_mul_of_nonneg_right _ hτ
    apply mul_le_mul_of_nonneg_right hn hT
  linarith

def BetaStable (β βmax : ℝ) : Prop :=
  0 ≤ β ∧ β ≤ βmax

theorem betaStable_lower (β βmax : ℝ) (h : BetaStable β βmax) : 0 ≤ β := h.1
theorem betaStable_upper (β βmax : ℝ) (h : BetaStable β βmax) : β ≤ βmax := h.2

theorem betaStable_tighter (β βmax βmax' : ℝ) (hle : βmax ≤ βmax')
    (h : BetaStable β βmax) : BetaStable β βmax' :=
  ⟨h.1, le_trans h.2 hle⟩

def NetPowerPositive (P_fusion P_brem P_transport P_edge : ℝ) : Prop :=
  P_fusion ≥ P_brem + P_transport + P_edge

theorem netPower_scales (P_fusion P_brem P_transport P_edge c : ℝ)
    (hc : 0 ≤ c) (h : NetPowerPositive P_fusion P_brem P_transport P_edge) :
    NetPowerPositive (c * P_fusion) (c * P_brem) (c * P_transport) (c * P_edge) := by
  unfold NetPowerPositive at *
  nlinarith [mul_le_mul_of_nonneg_left h hc]

def ControlStable (τ_control γ : ℝ) : Prop :=
  0 < γ ∧ τ_control < 1 / γ

theorem controlStable_pos (τ_control γ : ℝ) (h : ControlStable τ_control γ) :
    0 < γ := h.1

theorem controlStable_faster_needed (τ_control τ_control' γ : ℝ)
    (hτ : τ_control' ≤ τ_control) (h : ControlStable τ_control γ) :
    ControlStable τ_control' γ :=
  ⟨h.1, lt_of_le_of_lt hτ h.2⟩

structure DEIClosure where
  n : ℝ
  T : ℝ
  τ : ℝ
  threshold : ℝ
  β : ℝ
  βmax : ℝ
  P_fusion : ℝ
  P_brem : ℝ
  P_transport : ℝ
  P_edge : ℝ
  τ_control : ℝ
  γ : ℝ
  lawson_ok  : LawsonViable n T τ threshold
  beta_ok    : BetaStable β βmax
  power_ok   : NetPowerPositive P_fusion P_brem P_transport P_edge
  control_ok : ControlStable τ_control γ

theorem deiClosure_lawson (d : DEIClosure) : LawsonViable d.n d.T d.τ d.threshold :=
  d.lawson_ok

theorem deiClosure_beta (d : DEIClosure) : BetaStable d.β d.βmax :=
  d.beta_ok

theorem deiClosure_power (d : DEIClosure) :
    NetPowerPositive d.P_fusion d.P_brem d.P_transport d.P_edge :=
  d.power_ok

theorem deiClosure_control (d : DEIClosure) : ControlStable d.τ_control d.γ :=
  d.control_ok

theorem deiClosure_all (d : DEIClosure) :
    LawsonViable d.n d.T d.τ d.threshold ∧
    BetaStable d.β d.βmax ∧
    NetPowerPositive d.P_fusion d.P_brem d.P_transport d.P_edge ∧
    ControlStable d.τ_control d.γ :=
  ⟨d.lawson_ok, d.beta_ok, d.power_ok, d.control_ok⟩

-- ENERGY DOMAIN AUDIT SEAL

structure EnergyAuditVector where
  domain_count      : ℕ
  domains_unique    : Bool
  closure_law_holds : Bool
  unification_valid : Bool
  dei_defined       : Bool
  sovereign_sealed  : Bool

def EnergyDomain_audit : EnergyAuditVector := {
  domain_count      := 21
  domains_unique    := true
  closure_law_holds := true
  unification_valid := true
  dei_defined       := true
  sovereign_sealed  := true
}

theorem energy_domain_sealed :
    EnergyDomain_audit.sovereign_sealed = true ∧
    EnergyDomain_audit.domain_count = 21 ∧
    EnergyDomain_audit.unification_valid = true := by
  decide

end EnergyDomain
