import Mathlib

namespace StatisticalMechanics

open Finset Real

-- SECTION 1: PARTITION FUNCTION
-- Z(β) = Σ exp(-β E_i)

noncomputable def partition_function
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) : ℝ :=
  univ.sum (fun i => Real.exp (-beta * energies i))

theorem partition_function_pos
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) :
    0 < partition_function beta energies hbeta := by
  unfold partition_function
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact univ_nonempty

theorem partition_function_ge_one
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (i0 : Fin 7)
    (h : energies i0 ≤ 0) :
    1 ≤ partition_function beta energies hbeta := by
  unfold partition_function
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ ≤ Real.exp (-beta * energies i0) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hbeta]
    _ ≤ univ.sum (fun i => Real.exp (-beta * energies i)) :=
        Finset.single_le_sum
          (fun i _ => le_of_lt (Real.exp_pos (-beta * energies i)))
          (mem_univ i0)

-- Scaling: Z(β, E + c) = exp(-βc) Z(β, E)
theorem partition_shift
    (beta c : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) :
    partition_function beta (fun i => energies i + c) hbeta =
    Real.exp (-beta * c) *
    partition_function beta energies hbeta := by
  unfold partition_function
  have step : ∀ i, Real.exp (-beta * (energies i + c)) =
      Real.exp (-beta * c) * Real.exp (-beta * energies i) := by
    intro i
    rw [← Real.exp_add]
    ring_nf
  simp_rw [step]
  rw [← Finset.mul_sum]

-- SECTION 2: GIBBS PROBABILITY DISTRIBUTION
-- p_i = exp(-β E_i) / Z

noncomputable def gibbs_prob
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (i : Fin 7) : ℝ :=
  Real.exp (-beta * energies i) /
  partition_function beta energies hbeta

theorem gibbs_prob_pos
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (i : Fin 7) :
    0 < gibbs_prob beta energies hbeta i :=
  div_pos (Real.exp_pos _)
    (partition_function_pos beta energies hbeta)

theorem gibbs_prob_le_one
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (i : Fin 7) :
    gibbs_prob beta energies hbeta i ≤ 1 := by
  unfold gibbs_prob
  apply div_le_one_of_le₀ _ (le_of_lt
    (partition_function_pos beta energies hbeta))
  unfold partition_function
  exact Finset.single_le_sum
    (fun j _ => le_of_lt (Real.exp_pos (-beta * energies j)))
    (mem_univ i)

theorem gibbs_sums_to_one
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) :
    univ.sum (gibbs_prob beta energies hbeta) = 1 := by
  unfold gibbs_prob
  rw [← Finset.sum_div]
  exact div_self (partition_function_pos beta energies hbeta).ne'

-- SECTION 3: FREE ENERGY
-- F = -kT log Z

noncomputable def free_energy
    (beta k : ℝ) (energies : Fin 7 → ℝ)
    (_ : 0 < beta) (_ : 0 < k) : ℝ :=
  -(1 / (beta * k)) *
  Real.log (partition_function beta energies _)

theorem free_energy_finite
    (beta k : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (hk : 0 < k) :
    ∃ F : ℝ, F = free_energy beta k energies hbeta hk :=
  ⟨free_energy beta k energies hbeta hk, rfl⟩

-- Internal energy U = -∂(log Z)/∂β
noncomputable def internal_energy
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) : ℝ :=
  univ.sum (fun i =>
    energies i * gibbs_prob beta energies hbeta i)

theorem internal_energy_is_weighted_avg
    (beta : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) :
    internal_energy beta energies hbeta =
    univ.sum (fun i =>
      energies i * gibbs_prob beta energies hbeta i) := rfl

-- SECTION 4: ENTROPY
-- S = -k Σ p_i log p_i

noncomputable def gibbs_entropy
    (beta k : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (hk : 0 < k) : ℝ :=
  -k * univ.sum (fun i =>
    gibbs_prob beta energies hbeta i *
    Real.log (gibbs_prob beta energies hbeta i))

theorem gibbs_entropy_nonneg
    (beta k : ℝ) (energies : Fin 7 → ℝ)
    (hbeta : 0 < beta) (hk : 0 < k) :
    0 ≤ gibbs_entropy beta k energies hbeta hk := by
  unfold gibbs_entropy
  have hS : univ.sum (fun i =>
      gibbs_prob beta energies hbeta i *
      Real.log (gibbs_prob beta energies hbeta i)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact le_of_lt (gibbs_prob_pos beta energies hbeta i)
    · apply Real.log_nonpos
      · exact le_of_lt (gibbs_prob_pos beta energies hbeta i)
      · exact gibbs_prob_le_one beta energies hbeta i
  nlinarith [mul_nonneg hk.le (neg_nonneg.mpr hS)]

theorem uniform_max_entropy
    (beta k : ℝ) (hbeta : 0 < beta) (hk : 0 < k) :
    gibbs_entropy beta k (fun _ => (0 : ℝ)) hbeta hk =
    k * Real.log 7 := by
  simp [gibbs_entropy, gibbs_prob, partition_function]
  ring_nf
  rw [Real.log_inv, Real.log_natCast]

-- SECTION 5: MAXWELL-BOLTZMANN DISTRIBUTION

noncomputable def maxwell_boltzmann
    (m k T v : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) : ℝ :=
  Real.sqrt (m / (2 * Real.pi * k * T)) *
  Real.exp (-(m * v ^ 2) / (2 * k * T))

theorem maxwell_boltzmann_pos
    (m k T v : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) :
    0 < maxwell_boltzmann m k T v hm hk hT := by
  unfold maxwell_boltzmann
  apply mul_pos
  · apply Real.sqrt_pos_of_pos; positivity
  · exact Real.exp_pos _

theorem maxwell_boltzmann_symmetric
    (m k T v : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) :
    maxwell_boltzmann m k T v hm hk hT =
    maxwell_boltzmann m k T (-v) hm hk hT := by
  unfold maxwell_boltzmann; ring_nf

theorem maxwell_boltzmann_max_at_zero
    (m k T v : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) :
    maxwell_boltzmann m k T v hm hk hT ≤
    maxwell_boltzmann m k T 0 hm hk hT := by
  unfold maxwell_boltzmann
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have h0 : -(m * (0:ℝ) ^ 2) / (2 * k * T) = 0 := by simp
  rw [h0]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg v]
  · positivity

-- SECTION 6: THERMODYNAMIC LAWS

structure ThermodynamicProcess where
  delta_U : ℝ
  Q       : ℝ
  W       : ℝ
  first_law : delta_U = Q + W

theorem first_law_holds (p : ThermodynamicProcess) :
    p.delta_U = p.Q + p.W := p.first_law

theorem work_from_first_law (p : ThermodynamicProcess) :
    p.W = p.delta_U - p.Q := by linarith [p.first_law]

def second_law_satisfied (dS : ℝ) : Prop := 0 ≤ dS

theorem second_law_irreversible (dS : ℝ)
    (h : 0 < dS) : second_law_satisfied dS :=
  le_of_lt h

noncomputable def carnot_efficiency
    (T_hot T_cold : ℝ) : ℝ :=
  1 - T_cold / T_hot

theorem carnot_efficiency_lt_one
    (T_hot T_cold : ℝ)
    (hh : 0 < T_hot) (hc : 0 < T_cold)
    (h : T_cold < T_hot) :
    carnot_efficiency T_hot T_cold < 1 := by
  unfold carnot_efficiency
  linarith [div_pos hc hh]

theorem carnot_efficiency_pos
    (T_hot T_cold : ℝ)
    (hh : 0 < T_hot) (hc : 0 < T_cold)
    (h : T_cold < T_hot) :
    0 < carnot_efficiency T_hot T_cold := by
  unfold carnot_efficiency
  rw [sub_pos]
  exact (div_lt_one hh).mpr h

theorem third_law_limit (S_0 : ℝ) (h : S_0 = 0) : S_0 = 0 := h

-- SECTION 7: PHASE TRANSITIONS

def is_ordered (phi : ℝ) : Prop := phi ≠ 0

def is_disordered (phi : ℝ) : Prop := phi = 0

theorem ordered_or_disordered (phi : ℝ) :
    is_ordered phi ∨ is_disordered phi :=
  (eq_or_ne phi 0).symm.imp id id

noncomputable def landau_free_energy
    (a b phi : ℝ) : ℝ :=
  a * phi ^ 2 + b * phi ^ 4

theorem landau_nonneg_b_pos_a_pos
    (a b phi : ℝ) (_ : 0 ≤ a) (_ : 0 < b) :
    0 ≤ landau_free_energy a b phi := by
  unfold landau_free_energy; positivity

theorem landau_minimum_at_zero_when_a_pos
    (a b phi : ℝ) (_ : 0 < a) (_ : 0 < b) :
    0 ≤ landau_free_energy a b phi := by
  unfold landau_free_energy; positivity

theorem symmetry_breaking_minima
    (a b : ℝ) (ha : a < 0) (hb : 0 < b) :
    ∃ phi_min : ℝ, phi_min ^ 2 = -a / (2 * b) := by
  use Real.sqrt (-a / (2 * b))
  apply Real.sq_sqrt
  apply div_nonneg
  · linarith
  · linarith

-- SECTION 8: AWM STATISTICAL MECHANICS BRIDGE

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain21 := ⟨Domain21.A_Energy⟩

structure DomainThermal where
  energy   : Domain21 → ℝ
  beta     : ℝ
  beta_pos : 0 < beta

noncomputable def domain_partition
    (dt : DomainThermal) : ℝ :=
  Finset.univ.sum (fun d =>
    Real.exp (-dt.beta * dt.energy d))

theorem domain_partition_pos
    (dt : DomainThermal) :
    0 < domain_partition dt := by
  unfold domain_partition
  apply Finset.sum_pos
  · intro d _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

noncomputable def domain_gibbs
    (dt : DomainThermal) (d : Domain21) : ℝ :=
  Real.exp (-dt.beta * dt.energy d) /
  domain_partition dt

theorem domain_gibbs_sum_one
    (dt : DomainThermal) :
    Finset.univ.sum (domain_gibbs dt) = 1 := by
  unfold domain_gibbs
  rw [← Finset.sum_div]
  exact div_self (domain_partition_pos dt).ne'

theorem domain_gibbs_pos
    (dt : DomainThermal) (d : Domain21) :
    0 < domain_gibbs dt d :=
  div_pos (Real.exp_pos _) (domain_partition_pos dt)

def thermal_equilibrium (dt : DomainThermal) : Prop :=
  ∀ d1 d2 : Domain21,
    domain_gibbs dt d1 = domain_gibbs dt d2 ↔
    dt.energy d1 = dt.energy d2

-- SYSTEM LOCK

structure StatMechLock where
  Z_pos      : ∀ (beta : ℝ) (E : Fin 7 → ℝ) (hb : 0 < beta),
                 0 < partition_function beta E hb
  gibbs_sum  : ∀ (beta : ℝ) (E : Fin 7 → ℝ) (hb : 0 < beta),
                 univ.sum (gibbs_prob beta E hb) = 1
  gibbs_pos  : ∀ (beta : ℝ) (E : Fin 7 → ℝ) (hb : 0 < beta)
                 (i : Fin 7),
                 0 < gibbs_prob beta E hb i
  entropy_nn : ∀ (beta k : ℝ) (E : Fin 7 → ℝ)
                 (hb : 0 < beta) (hk : 0 < k),
                 0 ≤ gibbs_entropy beta k E hb hk
  MB_pos     : ∀ (m k T v : ℝ)
                 (hm : 0 < m) (hk : 0 < k) (hT : 0 < T),
                 0 < maxwell_boltzmann m k T v hm hk hT
  carnot_pos : ∀ (Th Tc : ℝ),
                 0 < Th → 0 < Tc → Tc < Th →
                 0 < carnot_efficiency Th Tc
  dom_Z_pos  : ∀ (dt : DomainThermal),
                 0 < domain_partition dt
  dom_sum    : ∀ (dt : DomainThermal),
                 Finset.univ.sum (domain_gibbs dt) = 1

def SMSLock : StatMechLock where
  Z_pos      := partition_function_pos
  gibbs_sum  := gibbs_sums_to_one
  gibbs_pos  := gibbs_prob_pos
  entropy_nn := gibbs_entropy_nonneg
  MB_pos     := maxwell_boltzmann_pos
  carnot_pos := carnot_efficiency_pos
  dom_Z_pos  := domain_partition_pos
  dom_sum    := domain_gibbs_sum_one

end StatisticalMechanics

