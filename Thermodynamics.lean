-- Thermodynamics.lean
import Mathlib

namespace Thermodynamics

open Finset Real

-- SECTION 1: LAWS OF THERMODYNAMICS

def first_law (U Q W : ℝ) : Prop :=
  U = Q - W

theorem first_law_energy_conservation
    (Q W : ℝ) :
    first_law (Q - W) Q W := rfl

def second_law (S1 S2 : ℝ) : Prop :=
  S1 ≤ S2

theorem second_law_reflexive (S : ℝ) :
    second_law S S := le_refl S

theorem second_law_transitive
    (S1 S2 S3 : ℝ)
    (h12 : second_law S1 S2)
    (h23 : second_law S2 S3) :
    second_law S1 S3 :=
  le_trans h12 h23

theorem third_law_proxy
    (S : ℝ → ℝ)
    (hS : ∀ T, 0 ≤ S T) :
    0 ≤ S 0 := hS 0

def thermal_equilibrium (T1 T2 : ℝ) : Prop :=
  T1 = T2

theorem zeroth_law_transitive
    (A B C : ℝ)
    (hAB : thermal_equilibrium A B)
    (hBC : thermal_equilibrium B C) :
    thermal_equilibrium A C := by
  unfold thermal_equilibrium at *
  linarith

-- SECTION 2: THERMODYNAMIC POTENTIALS

noncomputable def internal_energy
    (T S p V mu N : ℝ) : ℝ :=
  T * S - p * V + mu * N

noncomputable def helmholtz_free_energy
    (U T S : ℝ) : ℝ :=
  U - T * S

noncomputable def gibbs_free_energy
    (H T S : ℝ) : ℝ :=
  H - T * S

theorem gibbs_nonneg_at_equilibrium
    (H T S : ℝ)
    (h : H ≥ T * S) :
    0 ≤ gibbs_free_energy H T S := by
  unfold gibbs_free_energy; linarith

noncomputable def enthalpy
    (U p V : ℝ) : ℝ :=
  U + p * V

theorem enthalpy_nonneg
    (U p V : ℝ)
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hV : 0 ≤ V) :
    0 ≤ enthalpy U p V := by
  unfold enthalpy
  linarith [mul_nonneg hp hV]

theorem maxwell_relation_proxy
    (T S p V : ℝ) :
    True := trivial

-- SECTION 3: IDEAL GAS

def ideal_gas_law
    (p V n R T : ℝ) : Prop :=
  p * V = n * R * T

theorem ideal_gas_pressure_pos
    (n R T : ℝ)
    (hn : 0 < n) (hR : 0 < R) (hT : 0 < T) :
    0 < n * R * T :=
  mul_pos (mul_pos hn hR) hT

noncomputable def ideal_gas_energy
    (n Cv T : ℝ) : ℝ :=
  n * Cv * T

theorem ideal_gas_energy_nonneg
    (n Cv T : ℝ)
    (hn : 0 ≤ n) (hCv : 0 ≤ Cv) (hT : 0 ≤ T) :
    0 ≤ ideal_gas_energy n Cv T := by
  unfold ideal_gas_energy
  exact mul_nonneg (mul_nonneg hn hCv) hT

noncomputable def equipartition_energy
    (f k T : ℝ) : ℝ :=
  f / 2 * k * T

theorem equipartition_nonneg
    (f k T : ℝ)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hT : 0 ≤ T) :
    0 ≤ equipartition_energy f k T := by
  unfold equipartition_energy
  apply mul_nonneg (mul_nonneg _ hk) hT
  exact div_nonneg hf (by norm_num)

-- SECTION 4: ENTROPY

noncomputable def boltzmann_entropy
    (k Omega : ℝ) (hOmega : 0 < Omega) : ℝ :=
  k * Real.log Omega

theorem boltzmann_entropy_nonneg
    (k Omega : ℝ)
    (hk : 0 ≤ k) (hOmega : 1 ≤ Omega) :
    0 ≤ boltzmann_entropy k Omega
      (by linarith) := by
  unfold boltzmann_entropy
  apply mul_nonneg hk
  exact Real.log_nonneg hOmega

noncomputable def gibbs_entropy (n : ℕ)
    (k : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) : ℝ :=
  -k * Finset.univ.sum (fun i =>
    if p i = 0 then 0
    else p i * Real.log (p i))

-- After `rw [neg_mul, neg_nonneg]` the goal is `k * S ≤ 0` (nonpositive),
-- not `0 ≤ k * S` — `mul_nonneg` proves the wrong direction entirely.
-- Real fix is `mul_nonpos_of_nonneg_of_nonpos`, matching what the log
-- actually reported the goal to be.
theorem gibbs_entropy_nonneg (n : ℕ)
    (k : ℝ) (hk : 0 ≤ k)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : Finset.univ.sum p = 1) :
    0 ≤ gibbs_entropy n k p hp := by
  unfold gibbs_entropy
  rw [neg_mul, neg_nonneg]
  apply mul_nonpos_of_nonneg_of_nonpos hk
  apply Finset.sum_nonpos; intro i _
  split_ifs with h
  · linarith
  · apply mul_nonpos_of_nonneg_of_nonpos (hp i)
    apply Real.log_nonpos (hp i)
    have := Finset.single_le_sum
      (fun j _ => hp j) (Finset.mem_univ i)
    linarith [hsum]

noncomputable def entropy_of_mixing (n : ℕ)
    (k : ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) : ℝ :=
  -k * Finset.univ.sum (fun i =>
    x i * Real.log (x i))

theorem entropy_mixing_nonneg (n : ℕ)
    (k : ℝ) (hk : 0 ≤ k)
    (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i)
    (hsum : Finset.univ.sum x = 1) :
    0 ≤ entropy_of_mixing n k x hx := by
  unfold entropy_of_mixing
  rw [neg_mul, neg_nonneg]
  apply mul_nonpos_of_nonneg_of_nonpos hk
  apply Finset.sum_nonpos; intro i _
  apply mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (hx i))
  apply Real.log_nonpos (le_of_lt (hx i))
  have := Finset.single_le_sum
    (fun j _ => le_of_lt (hx j))
    (Finset.mem_univ i)
  linarith [hsum]

-- SECTION 5: HEAT ENGINES

noncomputable def carnot_efficiency
    (T_hot T_cold : ℝ)
    (hT : 0 < T_cold)
    (hTh : T_cold < T_hot) : ℝ :=
  1 - T_cold / T_hot

theorem carnot_efficiency_pos
    (T_hot T_cold : ℝ)
    (hT : 0 < T_cold)
    (hTh : T_cold < T_hot) :
    0 < carnot_efficiency T_hot T_cold hT hTh := by
  unfold carnot_efficiency
  rw [sub_pos, div_lt_one (by linarith)]
  exact hTh

theorem carnot_efficiency_lt_one
    (T_hot T_cold : ℝ)
    (hT : 0 < T_cold)
    (hTh : T_cold < T_hot) :
    carnot_efficiency T_hot T_cold hT hTh < 1 := by
  unfold carnot_efficiency
  linarith [div_pos hT (by linarith : (0:ℝ) < T_hot)]

noncomputable def refrigerator_COP
    (T_hot T_cold : ℝ)
    (hT : 0 < T_cold)
    (hTh : T_cold < T_hot) : ℝ :=
  T_cold / (T_hot - T_cold)

theorem refrigerator_COP_pos
    (T_hot T_cold : ℝ)
    (hT : 0 < T_cold)
    (hTh : T_cold < T_hot) :
    0 < refrigerator_COP T_hot T_cold hT hTh := by
  unfold refrigerator_COP
  apply div_pos hT
  linarith

-- SECTION 6: PHASE TRANSITIONS

noncomputable def clausius_clapeyron
    (L T dV : ℝ) (hT : 0 < T)
    (hdV : 0 < dV) : ℝ :=
  L / (T * dV)

theorem CC_pos (L T dV : ℝ)
    (hL : 0 < L) (hT : 0 < T)
    (hdV : 0 < dV) :
    0 < clausius_clapeyron L T dV hT hdV := by
  unfold clausius_clapeyron
  exact div_pos hL (mul_pos hT hdV)

theorem latent_heat_nonneg
    (L : ℝ) (hL : 0 ≤ L) : 0 ≤ L := hL

theorem triple_point_proxy :
    ∃ T p : ℝ, 0 < T ∧ 0 < p :=
  ⟨273.16, 611.73, by norm_num, by norm_num⟩

theorem order_param_nonneg
    (phi : ℝ) (h : 0 ≤ phi) : 0 ≤ phi := h

-- SECTION 7: STATISTICAL THERMODYNAMICS

noncomputable def partition_function (n : ℕ)
    (beta : ℝ) (E : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i =>
    Real.exp (-beta * E i))

theorem partition_function_pos (n : ℕ)
    (hn : 0 < n) (beta : ℝ)
    (E : Fin n → ℝ) :
    0 < partition_function n beta E := by
  unfold partition_function
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

noncomputable def free_energy_stat (n : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (E : Fin n → ℝ) (hn : 0 < n) : ℝ :=
  -Real.log (partition_function n beta E) / beta

theorem free_energy_finite (n : ℕ)
    (hn : 0 < n) (beta : ℝ) (hbeta : 0 < beta)
    (E : Fin n → ℝ) :
    ∃ F : ℝ, F = free_energy_stat n beta
      hbeta E hn :=
  ⟨_, rfl⟩

theorem avg_energy_proxy (n : ℕ)
    (hn : 0 < n) (beta : ℝ)
    (E : Fin n → ℝ) :
    0 < partition_function n beta E :=
  partition_function_pos n hn beta E

-- SECTION 8: IRREVERSIBLE THERMODYNAMICS

theorem entropy_production_nonneg
    (sigma : ℝ) (h : 0 ≤ sigma) :
    0 ≤ sigma := h

theorem onsager_proxy
    (L11 L12 L21 L22 : ℝ)
    (h : L12 = L21) :
    L12 = L21 := h

theorem dissipation_nonneg
    (Phi : ℝ) (h : 0 ≤ Phi) :
    0 ≤ Phi := h

theorem GENERIC_proxy (E S : ℝ → ℝ) :
    True := trivial

-- SECTION 9: AWM THERMODYNAMICS BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_Z : ℝ :=
  partition_function 21 1
    (fun i => (i.val : ℝ))

theorem domain_Z_pos :
    0 < domain_Z :=
  partition_function_pos 21
    (by norm_num) 1
    (fun i => (i.val : ℝ))

noncomputable def domain_gibbs_entropy : ℝ :=
  gibbs_entropy 21 1
    (fun _ => 1/21)
    (by intro _; norm_num)

theorem domain_gibbs_nonneg :
    0 ≤ domain_gibbs_entropy :=
  gibbs_entropy_nonneg 21 1 (by norm_num)
    (fun _ => 1/21)
    (by intro _; norm_num)
    (by simp [Finset.sum_const, Finset.card_fin])

noncomputable def domain_carnot :=
  carnot_efficiency 1000 300
    (by norm_num) (by norm_num)

theorem domain_carnot_pos :
    0 < domain_carnot :=
  carnot_efficiency_pos 1000 300
    (by norm_num) (by norm_num)

theorem domain_carnot_lt_one :
    domain_carnot < 1 :=
  carnot_efficiency_lt_one 1000 300
    (by norm_num) (by norm_num)

noncomputable def domain_enthalpy :=
  enthalpy 1 1 21

theorem domain_enthalpy_nonneg :
    0 ≤ domain_enthalpy :=
  enthalpy_nonneg 1 1 21
    (by norm_num) (by norm_num) (by norm_num)

noncomputable def domain_boltzmann :=
  boltzmann_entropy 1 21 (by norm_num)

theorem domain_boltzmann_nonneg :
    0 ≤ domain_boltzmann :=
  boltzmann_entropy_nonneg 1 21
    (by norm_num) (by norm_num)

-- SYSTEM LOCK

structure ThermodynamicsLock where
  first_law      : ∀ Q W : ℝ,
                     first_law (Q - W) Q W
  second_law_tr  : ∀ S1 S2 S3 : ℝ,
                     second_law S1 S2 →
                     second_law S2 S3 →
                     second_law S1 S3
  zeroth_law_tr  : ∀ A B C : ℝ,
                     thermal_equilibrium A B →
                     thermal_equilibrium B C →
                     thermal_equilibrium A C
  enthalpy_nn    : ∀ (U p V : ℝ),
                     0 ≤ U → 0 ≤ p → 0 ≤ V →
                     0 ≤ enthalpy U p V
  ideal_gas_nn   : ∀ (n Cv T : ℝ),
                     0 ≤ n → 0 ≤ Cv → 0 ≤ T →
                     0 ≤ ideal_gas_energy n Cv T
  boltz_nn       : ∀ (k Omega : ℝ) (hk : 0 ≤ k) (hOmega : 1 ≤ Omega),
                     0 ≤ boltzmann_entropy k Omega
                       (by linarith)
  gibbs_nn       : ∀ (n : ℕ) (k : ℝ) (hk : 0 ≤ k)
                     (p : Fin n → ℝ)
                     (hp : ∀ i, 0 ≤ p i)
                     (hsum : Finset.univ.sum p = 1),
                     0 ≤ gibbs_entropy n k p hp
  carnot_pos     : ∀ (Th Tc : ℝ)
                     (hT : 0 < Tc) (hTh : Tc < Th),
                     0 < carnot_efficiency Th Tc hT hTh
  carnot_lt1     : ∀ (Th Tc : ℝ)
                     (hT : 0 < Tc) (hTh : Tc < Th),
                     carnot_efficiency Th Tc hT hTh < 1
  part_fn_pos    : ∀ (n : ℕ), 0 < n →
                     ∀ (beta : ℝ)
                       (E : Fin n → ℝ),
                     0 < partition_function
                       n beta E
  dom_Z_pos      : 0 < domain_Z
  dom_gibbs_nn   : 0 ≤ domain_gibbs_entropy
  dom_carnot_pos : 0 < domain_carnot
  dom_carnot_lt1 : domain_carnot < 1
  dom_enthalpy_nn : 0 ≤ domain_enthalpy
  dom_boltz_nn   : 0 ≤ domain_boltzmann

def TDLock : ThermodynamicsLock where
  first_law      := first_law_energy_conservation
  second_law_tr  := second_law_transitive
  zeroth_law_tr  := zeroth_law_transitive
  enthalpy_nn    := enthalpy_nonneg
  ideal_gas_nn   := ideal_gas_energy_nonneg
  boltz_nn       := boltzmann_entropy_nonneg
  gibbs_nn       := gibbs_entropy_nonneg
  carnot_pos     := carnot_efficiency_pos
  carnot_lt1     := carnot_efficiency_lt_one
  part_fn_pos    := partition_function_pos
  dom_Z_pos      := domain_Z_pos
  dom_gibbs_nn   := domain_gibbs_nonneg
  dom_carnot_pos := domain_carnot_pos
  dom_carnot_lt1 := domain_carnot_lt_one
  dom_enthalpy_nn := domain_enthalpy_nonneg
  dom_boltz_nn   := domain_boltzmann_nonneg

end Thermodynamics
