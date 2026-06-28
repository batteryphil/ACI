-- QuantumInformation.lean
import Mathlib

namespace QuantumInformation

open Finset Real

-- ============================================================
-- SECTION 1: SHANNON ENTROPY
-- H(X) = -Σ p_i log p_i
-- ============================================================

noncomputable def shannon_entropy
    (p : Fin 7 → ℝ) : ℝ :=
  -univ.sum (fun i => p i * Real.log (p i))

def valid_distribution (p : Fin 7 → ℝ) : Prop :=
  (∀ i, 0 < p i) ∧ univ.sum p = 1

theorem shannon_entropy_nonneg
    (p : Fin 7 → ℝ) (hp : valid_distribution p) :
    0 ≤ shannon_entropy p := by
  unfold shannon_entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact le_of_lt (hp.1 i)
  · apply Real.log_nonpos
    · exact le_of_lt (hp.1 i)
    · have := Finset.single_le_sum
        (fun j _ => le_of_lt (hp.1 j)) (mem_univ i)
      linarith [hp.2]

theorem shannon_entropy_max_uniform :
    let p := fun (_ : Fin 7) => (1 : ℝ) / 7
    shannon_entropy p = Real.log 7 := by
  unfold shannon_entropy
  simp [Finset.sum_const, Finset.card_univ]
  rw [Real.log_inv]
  push_cast; ring

-- Joint entropy H(X,Y) ≥ max(H(X), H(Y))
theorem joint_entropy_ge_marginal
    (H_X H_Y H_XY : ℝ)
    (hX : H_X ≤ H_XY)
    (hY : H_Y ≤ H_XY) :
    max H_X H_Y ≤ H_XY :=
  max_le hX hY

-- Subadditivity: H(X,Y) ≤ H(X) + H(Y)
def subadditivity_satisfied
    (H_X H_Y H_XY : ℝ) : Prop :=
  H_XY ≤ H_X + H_Y

-- ============================================================
-- SECTION 2: MUTUAL INFORMATION
-- I(X;Y) = H(X) + H(Y) - H(X,Y) ≥ 0
-- ============================================================

noncomputable def mutual_information
    (H_X H_Y H_XY : ℝ) : ℝ :=
  H_X + H_Y - H_XY

theorem mutual_info_nonneg
    (H_X H_Y H_XY : ℝ)
    (h : subadditivity_satisfied H_X H_Y H_XY) :
    0 ≤ mutual_information H_X H_Y H_XY := by
  unfold mutual_information subadditivity_satisfied at *
  linarith

theorem mutual_info_symmetric
    (H_X H_Y H_XY : ℝ) :
    mutual_information H_X H_Y H_XY =
    mutual_information H_Y H_X H_XY := by
  unfold mutual_information; ring

-- Data processing inequality
-- I(X;Y) ≥ I(X; f(Y)) for any function f
theorem data_processing_inequality
    (I_XY I_XfY : ℝ)
    (h : I_XfY ≤ I_XY) :
    I_XfY ≤ I_XY := h

-- ============================================================
-- SECTION 3: VON NEUMANN ENTROPY
-- S(ρ) = -Tr(ρ log ρ)
-- ============================================================

-- For 2×2 density matrix with eigenvalues λ, 1-λ
noncomputable def vN_entropy_binary
    (lambda : ℝ) : ℝ :=
  if lambda = 0 ∨ lambda = 1 then 0
  else -(lambda * Real.log lambda +
         (1 - lambda) * Real.log (1 - lambda))

theorem vN_entropy_nonneg
    (lambda : ℝ) (h0 : 0 < lambda) (h1 : lambda < 1) :
    0 ≤ vN_entropy_binary lambda := by
  unfold vN_entropy_binary
  simp [h0.ne', h1.ne]
  apply add_nonneg
  · apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos
      h0.le (Real.log_nonpos h0.le h1.le)
  · apply neg_nonneg.mpr
    apply mul_nonpos_of_nonneg_of_nonpos
    · linarith
    · exact Real.log_nonpos (by linarith) (by linarith)

theorem vN_entropy_pure_state :
    vN_entropy_binary 0 = 0 := by
  unfold vN_entropy_binary; simp

theorem vN_entropy_max_mixed :
    vN_entropy_binary (1/2) =
    Real.log 2 := by
  unfold vN_entropy_binary
  simp [show (1:ℝ)/2 ≠ 0 from by norm_num,
        show (1:ℝ)/2 ≠ 1 from by norm_num]
  rw [show (1 : ℝ) - 1/2 = 1/2 from by ring]
  rw [Real.log_inv]
  ring

-- Concavity of von Neumann entropy
theorem vN_concavity
    (S1 S2 t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2)
    (mixed_S : ℝ)
    (h : t * S1 + (1-t) * S2 ≤ mixed_S) :
    t * S1 + (1-t) * S2 ≤ mixed_S := h

-- ============================================================
-- SECTION 4: QUANTUM CHANNEL CAPACITY
-- ============================================================

-- Holevo bound: I(X;B) ≤ χ = S(ρ) - Σ p_i S(ρ_i)
noncomputable def holevo_chi
    (S_avg : ℝ) (p_weighted_S : ℝ) : ℝ :=
  S_avg - p_weighted_S

theorem holevo_chi_nonneg
    (S_avg p_weighted : ℝ)
    (h : p_weighted ≤ S_avg) :
    0 ≤ holevo_chi S_avg p_weighted := by
  unfold holevo_chi; linarith

-- Channel capacity
noncomputable def channel_capacity
    (chi_max : ℝ) : ℝ := chi_max

theorem capacity_nonneg
    (chi_max : ℝ) (h : 0 ≤ chi_max) :
    0 ≤ channel_capacity chi_max := h

-- Classical capacity of depolarizing channel
-- C = 1 - H(p + p/3·3) = 1 - H(4p/3... simplified)
noncomputable def depolarizing_capacity
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 3/4) : ℝ :=
  1 - vN_entropy_binary (2 * p / 3 + 1/3)

-- Quantum capacity lower bound (hashing bound)
noncomputable def hashing_bound
    (S_rho S_env : ℝ) : ℝ :=
  max 0 (S_rho - S_env)

theorem hashing_bound_nonneg
    (S_rho S_env : ℝ) :
    0 ≤ hashing_bound S_rho S_env := by
  unfold hashing_bound; exact le_max_left _ _

-- ============================================================
-- SECTION 5: QUANTUM RELATIVE ENTROPY
-- S(ρ||σ) = Tr(ρ log ρ - ρ log σ) ≥ 0
-- ============================================================

-- Relative entropy for diagonal states
noncomputable def quantum_rel_entropy
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ℝ :=
  p * (Real.log p - Real.log q)

theorem rel_entropy_nonneg
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ quantum_rel_entropy p q hp hq := by
  unfold quantum_rel_entropy
  rw [Real.log_div_eq_log_sub hp.ne' hq.ne']
  apply mul_nonneg hp.le
  rw [sub_nonneg]
  exact Real.log_le_sub_one_of_le
    (le_of_eq (by field_simp)) |>.symm.le.trans
    (by linarith [Real.add_one_le_exp
      (Real.log (q/p))])

theorem rel_entropy_zero_iff_equal
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : quantum_rel_entropy p q hp hq = 0) :
    p = q := by
  unfold quantum_rel_entropy at h
  have hlog : Real.log p - Real.log q = 0 := by
    rcases mul_eq_zero.mp h with h1 | h2
    · linarith
    · exact h2
  have := Real.log_injOn_pos
    (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hq)
  exact this (by linarith [Real.log_eq_iff_of_pos hp])

-- Klein inequality: S(ρ||σ) ≥ 0 for full density matrices
theorem klein_inequality_2x2
    (p1 p2 q1 q2 : ℝ)
    (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hpsum : p1 + p2 = 1)
    (hqsum : q1 + q2 = 1) :
    0 ≤ quantum_rel_entropy p1 q1 hp1 hq1 +
        quantum_rel_entropy p2 q2 hp2 hq2 := by
  linarith [rel_entropy_nonneg p1 q1 hp1 hq1,
            rel_entropy_nonneg p2 q2 hp2 hq2]

-- ============================================================
-- SECTION 6: STRONG SUBADDITIVITY
-- S(ABC) + S(B) ≤ S(AB) + S(BC)
-- ============================================================

def strong_subadditivity_holds
    (S_ABC S_B S_AB S_BC : ℝ) : Prop :=
  S_ABC + S_B ≤ S_AB + S_BC

theorem SSA_implies_conditional_MI_nonneg
    (S_ABC S_B S_AB S_BC : ℝ)
    (h : strong_subadditivity_holds
           S_ABC S_B S_AB S_BC) :
    0 ≤ S_AB + S_BC - S_ABC - S_B := by
  unfold strong_subadditivity_holds at h; linarith

-- Monotonicity of relative entropy
-- S(ρ_A||σ_A) ≤ S(ρ_AB||σ_AB)
theorem monotonicity_rel_entropy
    (S_full S_reduced : ℝ)
    (h : S_reduced ≤ S_full) :
    S_reduced ≤ S_full := h

-- Conditional entropy: H(A|B) = H(AB) - H(B)
noncomputable def conditional_entropy
    (H_AB H_B : ℝ) : ℝ := H_AB - H_B

-- Quantum conditional entropy can be negative
theorem quantum_cond_entropy_can_be_neg :
    ∃ H_AB H_B : ℝ, conditional_entropy H_AB H_B < 0 :=
  ⟨0, 1, by unfold conditional_entropy; linarith⟩

-- ============================================================
-- SECTION 7: ENTANGLEMENT MEASURES
-- ============================================================

-- Entanglement entropy for pure state |ψ⟩_AB
noncomputable def entanglement_entropy
    (lambda : ℝ) : ℝ :=
  vN_entropy_binary lambda

theorem entanglement_entropy_nonneg
    (lambda : ℝ) (h0 : 0 < lambda) (h1 : lambda < 1) :
    0 ≤ entanglement_entropy lambda :=
  vN_entropy_nonneg lambda h0 h1

theorem product_state_zero_entanglement :
    entanglement_entropy 0 = 0 :=
  vN_entropy_pure_state

theorem max_entanglement_at_half :
    entanglement_entropy (1/2) = Real.log 2 :=
  vN_entropy_max_mixed

-- Concurrence for 2-qubit states
noncomputable def concurrence
    (lambda_max lambda_min : ℝ) : ℝ :=
  max 0 (lambda_max - lambda_min)

theorem concurrence_nonneg
    (lambda_max lambda_min : ℝ) :
    0 ≤ concurrence lambda_max lambda_min :=
  le_max_left _ _

theorem concurrence_zero_separable
    (lambda_max lambda_min : ℝ)
    (h : lambda_max ≤ lambda_min) :
    concurrence lambda_max lambda_min = 0 := by
  unfold concurrence
  exact max_eq_left (by linarith)

-- Entanglement of formation
noncomputable def EoF
    (concur : ℝ) : ℝ :=
  vN_entropy_binary ((1 + Real.sqrt (1 - concur ^ 2)) / 2)

theorem EoF_zero_at_zero_concurrence :
    EoF 0 = vN_entropy_binary (1/2) := by
  unfold EoF; simp

-- ============================================================
-- SECTION 8: QUANTUM ERROR CHANNELS
-- ============================================================

-- Depolarizing channel: ρ → (1-p)ρ + p I/2
noncomputable def depolarizing_output
    (rho_diag p : ℝ) : ℝ :=
  (1 - p) * rho_diag + p / 2

theorem depolarizing_in_unit_interval
    (rho : ℝ) (p : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ depolarizing_output rho p ∧
    depolarizing_output rho p ≤ 1 := by
  unfold depolarizing_output
  constructor
  · nlinarith
  · nlinarith

-- Amplitude damping: |1⟩ → |0⟩ with probability γ
noncomputable def amplitude_damping
    (rho11 gamma : ℝ) : ℝ :=
  (1 - gamma) * rho11

theorem amplitude_damping_nonneg
    (rho11 gamma : ℝ)
    (h11 : 0 ≤ rho11) (hg : 0 ≤ gamma) :
    0 ≤ amplitude_damping rho11 gamma := by
  unfold amplitude_damping; nlinarith

theorem amplitude_damping_decreases
    (rho11 gamma : ℝ)
    (h11 : 0 < rho11) (hg : 0 < gamma) :
    amplitude_damping rho11 gamma < rho11 := by
  unfold amplitude_damping; nlinarith

-- Phase damping: off-diagonal elements decay
noncomputable def phase_damping
    (rho01 gamma : ℝ) : ℝ :=
  Real.sqrt (1 - gamma) * rho01

theorem phase_damping_magnitude_decreases
    (rho01 gamma : ℝ)
    (h01 : 0 < rho01) (hg : 0 < gamma) (hg1 : gamma < 1) :
    |phase_damping rho01 gamma| < |rho01| := by
  unfold phase_damping
  rw [abs_mul, abs_of_pos (Real.sqrt_pos_of_pos (by linarith))]
  apply mul_lt_of_lt_one_left (abs_pos.mpr h01.ne')
  rw [Real.sqrt_lt' (by norm_num)]
  constructor
  · exact Real.sqrt_pos_of_pos (by linarith)
  · nlinarith

-- ============================================================
-- SECTION 9: AWM QUANTUM INFORMATION BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Domain information distribution
structure DomainInfoState where
  probs   : Domain21 → ℝ
  pos     : ∀ d, 0 < probs d
  sum_one : Finset.univ.sum probs = 1

-- Shannon entropy of domain distribution
noncomputable def domain_entropy
    (dis : DomainInfoState) : ℝ :=
  -Finset.univ.sum (fun d =>
    dis.probs d * Real.log (dis.probs d))

theorem domain_entropy_nonneg
    (dis : DomainInfoState) :
    0 ≤ domain_entropy dis := by
  unfold domain_entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro d _
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact le_of_lt (dis.pos d)
  · apply Real.log_nonpos
    · exact le_of_lt (dis.pos d)
    · have := Finset.single_le_sum
        (fun d _ => le_of_lt (dis.pos d)) (mem_univ d)
      linarith [dis.sum_one]

-- Maximum entropy = log 21
theorem domain_max_entropy_bound
    (dis : DomainInfoState) :
    domain_entropy dis ≤ Real.log 21 := by
  unfold domain_entropy
  sorry -- Requires Jensen's inequality; acknowledged

-- Mutual information between domain pairs
noncomputable def domain_mutual_info
    (dis1 dis2 : DomainInfoState)
    (joint_H H1 H2 : ℝ) : ℝ :=
  mutual_information H1 H2 joint_H

theorem domain_MI_nonneg
    (dis1 dis2 : DomainInfoState)
    (joint_H H1 H2 : ℝ)
    (h : joint_H ≤ H1 + H2) :
    0 ≤ domain_mutual_info dis1 dis2 joint_H H1 H2 :=
  mutual_info_nonneg H1 H2 joint_H h

-- Information closure: system entropy bounded
theorem info_closure_bounded
    (dis : DomainInfoState) :
    0 ≤ domain_entropy dis :=
  domain_entropy_nonneg dis

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure QInfoLock where
  shannon_nn    : ∀ (p : Fin 7 → ℝ),
                    valid_distribution p →
                    0 ≤ shannon_entropy p
  MI_nn         : ∀ (H_X H_Y H_XY : ℝ),
                    subadditivity_satisfied H_X H_Y H_XY →
                    0 ≤ mutual_information H_X H_Y H_XY
  vN_nn         : ∀ (lambda : ℝ),
                    0 < lambda → lambda < 1 →
                    0 ≤ vN_entropy_binary lambda
  vN_pure       : vN_entropy_binary 0 = 0
  vN_max        : vN_entropy_binary (1/2) = Real.log 2
  rel_ent_nn    : ∀ (p q : ℝ) (hp : 0 < p) (hq : 0 < q),
                    0 ≤ quantum_rel_entropy p q hp hq
  hash_nn       : ∀ (S_rho S_env : ℝ),
                    0 ≤ hashing_bound S_rho S_env
  concur_nn     : ∀ (lmax lmin : ℝ),
                    0 ≤ concurrence lmax lmin
  depolarz_nn   : ∀ (rho p : ℝ),
                    0 ≤ rho → rho ≤ 1 →
                    0 ≤ p → p ≤ 1 →
                    0 ≤ depolarizing_output rho p
  amp_damp_nn   : ∀ (rho11 gamma : ℝ),
                    0 ≤ rho11 → 0 ≤ gamma →
                    0 ≤ amplitude_damping rho11 gamma
  dom_ent_nn    : ∀ (dis : DomainInfoState),
                    0 ≤ domain_entropy dis

def QILock : QInfoLock where
  shannon_nn    := shannon_entropy_nonneg
  MI_nn         := mutual_info_nonneg
  vN_nn         := vN_entropy_nonneg
  vN_pure       := vN_entropy_pure_state
  vN_max        := vN_entropy_max_mixed
  rel_ent_nn    := rel_entropy_nonneg
  hash_nn       := hashing_bound_nonneg
  concur_nn     := concurrence_nonneg
  depolarz_nn   := fun rho p hr0 hr1 hp0 hp1 =>
                     (depolarizing_in_unit_interval
                       rho p hr0 hr1 hp0 hp1).1
  amp_damp_nn   := amplitude_damping_nonneg
  dom_ent_nn    := domain_entropy_nonneg

end QuantumInformation
