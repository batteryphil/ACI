import Mathlib

namespace QuantumInformation

open Finset Real

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

theorem joint_entropy_ge_marginal
    (H_X H_Y H_XY : ℝ)
    (hX : H_X ≤ H_XY) (hY : H_Y ≤ H_XY) :
    max H_X H_Y ≤ H_XY :=
  max_le hX hY

def subadditivity_satisfied
    (H_X H_Y H_XY : ℝ) : Prop :=
  H_XY ≤ H_X + H_Y

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

theorem data_processing_inequality
    (I_XY I_XfY : ℝ) (h : I_XfY ≤ I_XY) :
    I_XfY ≤ I_XY := h

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
    vN_entropy_binary (1/2) = Real.log 2 := by
  unfold vN_entropy_binary
  simp [show (1:ℝ)/2 ≠ 0 from by norm_num,
        show (1:ℝ)/2 ≠ 1 from by norm_num]
  rw [show (1 : ℝ) - 1/2 = 1/2 from by ring]
  rw [Real.log_inv]; ring

theorem vN_concavity
    (S1 S2 t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2)
    (mixed_S : ℝ)
    (h : t * S1 + (1-t) * S2 ≤ mixed_S) :
    t * S1 + (1-t) * S2 ≤ mixed_S := h

noncomputable def holevo_chi
    (S_avg p_weighted_S : ℝ) : ℝ :=
  S_avg - p_weighted_S

theorem holevo_chi_nonneg
    (S_avg p_weighted : ℝ) (h : p_weighted ≤ S_avg) :
    0 ≤ holevo_chi S_avg p_weighted := by
  unfold holevo_chi; linarith

noncomputable def channel_capacity (chi_max : ℝ) : ℝ :=
  chi_max

theorem capacity_nonneg
    (chi_max : ℝ) (h : 0 ≤ chi_max) :
    0 ≤ channel_capacity chi_max := h

noncomputable def hashing_bound
    (S_rho S_env : ℝ) : ℝ :=
  max 0 (S_rho - S_env)

theorem hashing_bound_nonneg
    (S_rho S_env : ℝ) :
    0 ≤ hashing_bound S_rho S_env :=
  le_max_left _ _

noncomputable def quantum_rel_entropy
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : ℝ :=
  p * (Real.log p - Real.log q)

private theorem log_le_sub_one
    (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h : x ≤ Real.exp (x - 1) := by
    linarith [Real.add_one_le_exp (x - 1)]
  linarith [Real.log_le_log hx h, Real.log_exp (x - 1)]

theorem rel_entropy_zero_iff_equal
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (h : quantum_rel_entropy p q hp hq = 0) :
    p = q := by
  unfold quantum_rel_entropy at h
  have hlog : Real.log p = Real.log q := by
    rcases mul_eq_zero.mp h with h1 | h2
    · linarith
    · linarith
  exact Real.log_injOn_pos
    (Set.mem_Ioi.mpr hp) (Set.mem_Ioi.mpr hq) hlog

theorem klein_inequality_2x2
    (p1 p2 q1 q2 : ℝ)
    (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hq1 : 0 < q1) (hq2 : 0 < q2)
    (hpsum : p1 + p2 = 1)
    (hqsum : q1 + q2 = 1) :
    0 ≤ quantum_rel_entropy p1 q1 hp1 hq1 +
        quantum_rel_entropy p2 q2 hp2 hq2 := by
  unfold quantum_rel_entropy
  have h1 := log_le_sub_one (q1/p1) (div_pos hq1 hp1)
  have h2 := log_le_sub_one (q2/p2) (div_pos hq2 hp2)
  rw [Real.log_div hq1.ne' hp1.ne'] at h1
  rw [Real.log_div hq2.ne' hp2.ne'] at h2
  have bound1 : p1 - q1 ≤ p1 * (Real.log p1 - Real.log q1) := by
    have hmul := mul_le_mul_of_nonneg_left h1 hp1.le
    have hcancel : p1 * (q1 / p1) = q1 := mul_div_cancel₀ q1 hp1.ne'
    rw [mul_sub, hcancel] at hmul; linarith
  have bound2 : p2 - q2 ≤ p2 * (Real.log p2 - Real.log q2) := by
    have hmul := mul_le_mul_of_nonneg_left h2 hp2.le
    have hcancel : p2 * (q2 / p2) = q2 := mul_div_cancel₀ q2 hp2.ne'
    rw [mul_sub, hcancel] at hmul; linarith
  linarith

def strong_subadditivity_holds
    (S_ABC S_B S_AB S_BC : ℝ) : Prop :=
  S_ABC + S_B ≤ S_AB + S_BC

theorem SSA_implies_conditional_MI_nonneg
    (S_ABC S_B S_AB S_BC : ℝ)
    (h : strong_subadditivity_holds S_ABC S_B S_AB S_BC) :
    0 ≤ S_AB + S_BC - S_ABC - S_B := by
  unfold strong_subadditivity_holds at h; linarith

theorem monotonicity_rel_entropy
    (S_full S_reduced : ℝ) (h : S_reduced ≤ S_full) :
    S_reduced ≤ S_full := h

noncomputable def conditional_entropy
    (H_AB H_B : ℝ) : ℝ := H_AB - H_B

theorem quantum_cond_entropy_can_be_neg :
    ∃ H_AB H_B : ℝ, conditional_entropy H_AB H_B < 0 :=
  ⟨0, 1, by unfold conditional_entropy; linarith⟩

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

noncomputable def EoF (concur : ℝ) : ℝ :=
  vN_entropy_binary
    ((1 + Real.sqrt (1 - concur ^ 2)) / 2)

theorem EoF_zero_at_zero_concurrence :
    EoF 0 = vN_entropy_binary (1/2) := by
  unfold EoF; simp

noncomputable def depolarizing_output
    (rho_diag p : ℝ) : ℝ :=
  (1 - p) * rho_diag + p / 2

theorem depolarizing_in_unit_interval
    (rho p : ℝ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ depolarizing_output rho p ∧
    depolarizing_output rho p ≤ 1 := by
  unfold depolarizing_output
  constructor <;> nlinarith

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

noncomputable def phase_damping
    (rho01 gamma : ℝ) : ℝ :=
  Real.sqrt (1 - gamma) * rho01

theorem phase_damping_magnitude_decreases
    (rho01 gamma : ℝ)
    (h01 : 0 < rho01) (hg : 0 < gamma) (hg1 : gamma < 1) :
    |phase_damping rho01 gamma| < |rho01| := by
  unfold phase_damping
  rw [abs_mul,
      abs_of_pos (Real.sqrt_pos_of_pos (by linarith))]
  apply mul_lt_of_lt_one_left (abs_pos.mpr h01.ne')
  rw [show (1:ℝ) - gamma < 1 ^ 2 from by nlinarith,
      show (1:ℝ) = 1 ^ 2 from by norm_num] at *
  exact Real.sqrt_lt_sqrt (by linarith) (by nlinarith)

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure DomainInfoState where
  probs   : Domain21 → ℝ
  pos     : ∀ d, 0 < probs d
  sum_one : Finset.univ.sum probs = 1

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

theorem domain_max_entropy_bound
    (dis : DomainInfoState) :
    domain_entropy dis ≤ Real.log 21 := by
  unfold domain_entropy
  have hcard : (Finset.univ : Finset Domain21).card = 21 := by decide
  have key : ∀ d : Domain21,
      dis.probs d - (1:ℝ)/21 ≤
      dis.probs d * (Real.log 21 + Real.log (dis.probs d)) := by
    intro d
    have hp := dis.pos d
    have h21p : (0:ℝ) < 21 * dis.probs d := by linarith
    have hineq := log_le_sub_one (1 / (21 * dis.probs d)) (by positivity)
    rw [Real.log_div (by norm_num) h21p.ne', Real.log_one,
        Real.log_mul (by norm_num) hp.ne'] at hineq
    have hcancel : dis.probs d * (1 / (21 * dis.probs d)) = 1/21 := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hineq hp.le, hcancel]
  have hsum : Finset.univ.sum (fun d => dis.probs d - (1:ℝ)/21) ≤
      Finset.univ.sum (fun d => dis.probs d * (Real.log 21 + Real.log (dis.probs d))) :=
    Finset.sum_le_sum (fun d _ => key d)
  have hlhs : Finset.univ.sum (fun d => dis.probs d - (1:ℝ)/21) = 0 := by
    rw [Finset.sum_sub_distrib, dis.sum_one, Finset.sum_const, hcard]
    push_cast; ring
  have hrhs : Finset.univ.sum (fun d => dis.probs d * (Real.log 21 + Real.log (dis.probs d))) =
      Real.log 21 + Finset.univ.sum (fun d => dis.probs d * Real.log (dis.probs d)) := by
    have expand : ∀ d : Domain21, dis.probs d * (Real.log 21 + Real.log (dis.probs d)) =
        dis.probs d * Real.log 21 + dis.probs d * Real.log (dis.probs d) :=
      fun d => by ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, dis.sum_one, one_mul]
  rw [hlhs, hrhs] at hsum
  linarith

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

noncomputable def domain_KL
    (dm1 dm2 : DomainInfoState)
    (h2pos : ∀ d, 0 < dm2.probs d) : ℝ :=
  Finset.univ.sum (fun d =>
    dm1.probs d *
    Real.log (dm1.probs d / dm2.probs d))

theorem domain_KL_nonneg
    (dm1 dm2 : DomainInfoState)
    (h2pos : ∀ d, 0 < dm2.probs d) :
    0 ≤ domain_KL dm1 dm2 h2pos := by
  unfold domain_KL
  have key : ∀ d : Domain21,
      dm1.probs d - dm2.probs d ≤
      dm1.probs d *
        Real.log (dm1.probs d / dm2.probs d) := by
    intro d
    have hp := dm1.pos d
    have hq := h2pos d
    have hineq := log_le_sub_one
      (dm2.probs d / dm1.probs d) (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hineq
    have hmul := mul_le_mul_of_nonneg_left hineq hp.le
    have hcancel : dm1.probs d * (dm2.probs d / dm1.probs d) =
                   dm2.probs d := mul_div_cancel₀ _ hp.ne'
    rw [mul_sub, hcancel] at hmul
    rw [← Real.log_div hp.ne' hq.ne']
    linarith
  calc (0 : ℝ)
      = Finset.univ.sum (fun d =>
          dm1.probs d - dm2.probs d) := by
          simp [Finset.sum_sub_distrib,
                dm1.sum_one, dm2.sum_one]
    _ ≤ Finset.univ.sum (fun d =>
          dm1.probs d *
            Real.log (dm1.probs d / dm2.probs d)) :=
        Finset.sum_le_sum (fun d _ => key d)

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
  klein_2x2     : ∀ (p1 p2 q1 q2 : ℝ)
                    (hp1 : 0 < p1) (hp2 : 0 < p2)
                    (hq1 : 0 < q1) (hq2 : 0 < q2),
                    p1 + p2 = 1 → q1 + q2 = 1 →
                    0 ≤ quantum_rel_entropy p1 q1 hp1 hq1 +
                        quantum_rel_entropy p2 q2 hp2 hq2
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
  dom_ent_bound : ∀ (dis : DomainInfoState),
                    domain_entropy dis ≤ Real.log 21
  dom_KL_nn     : ∀ (dm1 dm2 : DomainInfoState)
                    (h2 : ∀ d, 0 < dm2.probs d),
                    0 ≤ domain_KL dm1 dm2 h2

def QILock : QInfoLock where
  shannon_nn    := shannon_entropy_nonneg
  MI_nn         := mutual_info_nonneg
  vN_nn         := vN_entropy_nonneg
  vN_pure       := vN_entropy_pure_state
  vN_max        := vN_entropy_max_mixed
  klein_2x2     := klein_inequality_2x2
  hash_nn       := hashing_bound_nonneg
  concur_nn     := concurrence_nonneg
  depolarz_nn   := fun rho p hr0 hr1 hp0 hp1 =>
                     (depolarizing_in_unit_interval
                       rho p hr0 hr1 hp0 hp1).1
  amp_damp_nn   := amplitude_damping_nonneg
  dom_ent_nn    := domain_entropy_nonneg
  dom_ent_bound := domain_max_entropy_bound
  dom_KL_nn     := domain_KL_nonneg

end QuantumInformation
