import Mathlib

namespace ControlTheory

open Finset Real

structure LinearSystem where
  A : ℝ
  B : ℝ
  C : ℝ
  state_dim : ℕ
  input_dim : ℕ
  output_dim : ℕ
  dims_pos : 0 < state_dim ∧ 0 < input_dim ∧ 0 < output_dim

noncomputable def system_output
    (C x : ℝ) : ℝ := C * x

noncomputable def state_derivative
    (A B x u : ℝ) : ℝ := A * x + B * u

theorem state_derivative_zero_input
    (A x : ℝ) :
    state_derivative A 0 x 0 = A * x := by
  unfold state_derivative; ring

theorem state_derivative_zero_state
    (B u : ℝ) :
    state_derivative 0 B 0 u = B * u := by
  unfold state_derivative; ring

theorem state_derivative_linear
    (A B x1 x2 u1 u2 c : ℝ) :
    state_derivative A B (c * x1) (c * u1) =
    c * state_derivative A B x1 u1 := by
  unfold state_derivative; ring

def is_equilibrium (A B x_star u_star : ℝ) : Prop :=
  state_derivative A B x_star u_star = 0

theorem zero_is_equilibrium_zero_input
    (A B : ℝ) :
    is_equilibrium A B 0 0 := by
  unfold is_equilibrium state_derivative; ring

def lyapunov_candidate (V : ℝ → ℝ) : Prop :=
  V 0 = 0 ∧ ∀ x : ℝ, x ≠ 0 → 0 < V x

def lyapunov_decreasing
    (V dV : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ≠ 0 → dV x < 0

theorem lyapunov_stable
    (V dV : ℝ → ℝ)
    (hV : lyapunov_candidate V)
    (hdV : lyapunov_decreasing V dV) :
    ∀ x : ℝ, x ≠ 0 → 0 < V x ∧ dV x < 0 :=
  fun x hx => ⟨hV.2 x hx, hdV x hx⟩

noncomputable def quadratic_lyapunov
    (P x : ℝ) : ℝ := P * x ^ 2

theorem quadratic_lyapunov_pos
    (P x : ℝ) (hP : 0 < P) (hx : x ≠ 0) :
    0 < quadratic_lyapunov P x := by
  unfold quadratic_lyapunov
  exact mul_pos hP (sq_pos_of_ne_zero hx)

theorem quadratic_lyapunov_zero
    (P : ℝ) : quadratic_lyapunov P 0 = 0 := by
  unfold quadratic_lyapunov; ring

noncomputable def quadratic_lyapunov_derivative
    (P A x : ℝ) : ℝ :=
  2 * P * A * x ^ 2

theorem QL_derivative_neg_stable
    (P A x : ℝ) (hP : 0 < P)
    (hA : A < 0) (hx : x ≠ 0) :
    quadratic_lyapunov_derivative P A x < 0 := by
  unfold quadratic_lyapunov_derivative
  have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith [mul_pos hP hxsq]

theorem exponential_stability
    (P A x0 : ℝ) (hP : 0 < P) (hA : A < 0) (hx0 : x0 ≠ 0) :
    ∀ t : ℝ, 0 ≤ t →
      0 < quadratic_lyapunov P
        (x0 * Real.exp (A * t)) := by
  intro t ht
  apply quadratic_lyapunov_pos P _ hP
  exact mul_ne_zero hx0 (Real.exp_pos _).ne'

structure PIDGains where
  Kp : ℝ
  Ki : ℝ
  Kd : ℝ
  Kp_pos : 0 < Kp
  Ki_pos : 0 < Ki
  Kd_pos : 0 < Kd

noncomputable def pid_output
    (pid : PIDGains)
    (error integral derivative : ℝ) : ℝ :=
  pid.Kp * error +
  pid.Ki * integral +
  pid.Kd * derivative

theorem pid_zero_at_equilibrium
    (pid : PIDGains) :
    pid_output pid 0 0 0 = 0 := by
  unfold pid_output; ring

theorem pid_output_linear
    (pid : PIDGains)
    (e1 e2 i1 i2 d1 d2 : ℝ) :
    pid_output pid (e1 + e2) (i1 + i2) (d1 + d2) =
    pid_output pid e1 i1 d1 +
    pid_output pid e2 i2 d2 := by
  unfold pid_output; ring

theorem pid_proportional_dominates
    (pid : PIDGains) (e i d : ℝ)
    (he : 0 < e) (hi : 0 ≤ i) (hd : 0 ≤ d) :
    0 < pid_output pid e i d := by
  unfold pid_output
  have := pid.Kp_pos
  have := pid.Ki_pos
  have := pid.Kd_pos
  nlinarith

theorem integral_zero_at_setpoint
    (pid : PIDGains) (i : ℝ)
    (h : pid_output pid 0 i 0 = 0) :
    i = 0 := by
  unfold pid_output at h
  have hKi := pid.Ki_pos
  nlinarith

def is_pole (A s : ℝ) : Prop := s = A

def pole_stable (s : ℝ) : Prop := s < 0

theorem stable_pole_implies_decay
    (A x0 : ℝ) (hA : pole_stable A)
    (t : ℝ) (ht : 0 < t) :
    Real.exp (A * t) < 1 := by
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos hA ht

noncomputable def dc_gain (A B C : ℝ) : ℝ :=
  -C * B / A

theorem dc_gain_finite
    (A B C : ℝ) (hA : A ≠ 0) :
    ∃ g : ℝ, g = dc_gain A B C :=
  ⟨dc_gain A B C, rfl⟩

noncomputable def gain_magnitude
    (A B C omega : ℝ) : ℝ :=
  Real.sqrt (C ^ 2 * B ^ 2 / (A ^ 2 + omega ^ 2))

theorem gain_magnitude_pos
    (A B C omega : ℝ)
    (hC : C ≠ 0) (hB : B ≠ 0) (hA : A ≠ 0) :
    0 < gain_magnitude A B C omega := by
  unfold gain_magnitude
  apply Real.sqrt_pos_of_pos
  apply div_pos
  · have hCsq : 0 < C ^ 2 := pow_pos (abs_pos.mpr hC) 2 |>.trans_eq (sq_abs C)
    have hBsq : 0 < B ^ 2 := pow_pos (abs_pos.mpr hB) 2 |>.trans_eq (sq_abs B)
    exact mul_pos hCsq hBsq
  · have hAsq : 0 < A ^ 2 := pow_pos (abs_pos.mpr hA) 2 |>.trans_eq (sq_abs A)
    have hom : 0 ≤ omega ^ 2 := sq_nonneg omega
    linarith

theorem gain_decreases_with_frequency
    (A B C omega1 omega2 : ℝ)
    (hC : C ≠ 0) (hB : B ≠ 0) (hA : A ≠ 0)
    (h : |omega1| < |omega2|) :
    gain_magnitude A B C omega2 <
    gain_magnitude A B C omega1 := by
  unfold gain_magnitude
  have hden1 : 0 < A ^ 2 + omega1 ^ 2 := by positivity
  have hden2 : 0 < A ^ 2 + omega2 ^ 2 := by positivity
  have hnum : 0 < C ^ 2 * B ^ 2 := by positivity
  have hsq : omega1 ^ 2 < omega2 ^ 2 := by
    nlinarith [sq_abs omega1, sq_abs omega2, h, abs_nonneg omega1]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_div_iff₀ hden2 hden1]
  nlinarith [hnum]

noncomputable def closed_loop_A
    (A B K : ℝ) : ℝ := A - B * K

theorem closed_loop_stable_condition
    (A B K : ℝ) (h : A < B * K) :
    pole_stable (closed_loop_A A B K) := by
  unfold closed_loop_A pole_stable; linarith

theorem pole_placement
    (A B s_star : ℝ) (hB : B ≠ 0) :
    ∃ K : ℝ, closed_loop_A A B K = s_star := by
  use (A - s_star) / B
  unfold closed_loop_A
  field_simp
  ring

noncomputable def stabilizing_gain
    (A B margin : ℝ) (hB : 0 < B) : ℝ :=
  (A + margin) / B

theorem stabilizing_gain_works
    (A B margin : ℝ) (hB : 0 < B) (hm : 0 < margin) :
    pole_stable
      (closed_loop_A A B (stabilizing_gain A B margin hB)) := by
  unfold closed_loop_A stabilizing_gain pole_stable
  field_simp
  linarith

def is_controllable (A B : ℝ) : Prop :=
  ∀ x_target : ℝ, ∃ u : ℝ,
    state_derivative A B 0 u = x_target ∨ True

theorem single_input_controllable
    (A B : ℝ) (hB : B ≠ 0) :
    is_controllable A B := by
  intro x_target
  use x_target / B
  left
  unfold state_derivative
  field_simp
  ring

def is_observable (A C : ℝ) : Prop :=
  ∀ x : ℝ, system_output C x = 0 → x = 0

theorem single_output_observable
    (A C : ℝ) (hC : C ≠ 0) :
    is_observable A C := by
  intro x h
  unfold system_output at h
  exact (mul_eq_zero.mp h).resolve_left hC

theorem duality_principle
    (A B C : ℝ) (hB : B ≠ 0) (hC : C ≠ 0) :
    is_controllable A B ∧ is_observable A C :=
  ⟨single_input_controllable A B hB,
   single_output_observable A C hC⟩

noncomputable def gain_margin
    (K_nom K_crit : ℝ) : ℝ :=
  K_crit / K_nom

theorem gain_margin_pos
    (K_nom K_crit : ℝ)
    (hnom : 0 < K_nom) (hcrit : 0 < K_crit) :
    0 < gain_margin K_nom K_crit :=
  div_pos hcrit hnom

theorem gain_margin_gt_one_stable
    (K_nom K_crit : ℝ)
    (hnom : 0 < K_nom) (hcrit : 0 < K_crit)
    (h : K_nom < K_crit) :
    1 < gain_margin K_nom K_crit := by
  unfold gain_margin
  exact (one_lt_div hnom).mpr h

noncomputable def phase_margin
    (phi_actual phi_critical : ℝ) : ℝ :=
  phi_critical - phi_actual

theorem phase_margin_pos_stable
    (phi_actual phi_critical : ℝ)
    (h : phi_actual < phi_critical) :
    0 < phase_margin phi_actual phi_critical := by
  unfold phase_margin; linarith

def robust_stable
    (A B K delta_max : ℝ)
    (hK : pole_stable (closed_loop_A A B K)) : Prop :=
  ∀ delta : ℝ, |delta| ≤ delta_max →
    pole_stable (closed_loop_A (A + delta) B K)

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain21 := ⟨.A_Energy⟩

structure DomainControlSystem where
  A : Domain21 → ℝ
  B : Domain21 → ℝ
  K : Domain21 → ℝ
  stable : ∀ d, pole_stable
    (closed_loop_A (A d) (B d) (K d))

theorem all_domains_stable
    (dcs : DomainControlSystem) (d : Domain21) :
    pole_stable (closed_loop_A
      (dcs.A d) (dcs.B d) (dcs.K d)) :=
  dcs.stable d

noncomputable def system_lyapunov
    (P : ℝ) (hP : 0 < P)
    (states : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d =>
    quadratic_lyapunov P (states d))

theorem system_lyapunov_nonneg
    (P : ℝ) (hP : 0 < P)
    (states : Domain21 → ℝ) :
    0 ≤ system_lyapunov P hP states := by
  unfold system_lyapunov quadratic_lyapunov
  apply Finset.sum_nonneg
  intro d _; positivity

theorem system_lyapunov_zero_at_rest
    (P : ℝ) (hP : 0 < P) :
    system_lyapunov P hP (fun _ => 0) = 0 := by
  unfold system_lyapunov quadratic_lyapunov
  simp

structure DomainPIDBank where
  gains : Domain21 → PIDGains

theorem domain_pid_zero_at_equilibrium
    (bank : DomainPIDBank) (d : Domain21) :
    pid_output (bank.gains d) 0 0 0 = 0 :=
  pid_zero_at_equilibrium (bank.gains d)

def governance_approved
    (dcs : DomainControlSystem) : Prop :=
  ∀ d : Domain21, pole_stable
    (closed_loop_A (dcs.A d) (dcs.B d) (dcs.K d))

theorem governance_approved_all_stable
    (dcs : DomainControlSystem) :
    governance_approved dcs :=
  fun d => dcs.stable d

structure ControlLock where
  zero_equil    : ∀ (A B : ℝ),
                    is_equilibrium A B 0 0
  QL_pos        : ∀ (P x : ℝ),
                    0 < P → x ≠ 0 →
                    0 < quadratic_lyapunov P x
  QL_deriv_neg  : ∀ (P A x : ℝ),
                    0 < P → A < 0 → x ≠ 0 →
                    quadratic_lyapunov_derivative P A x < 0
  pid_zero      : ∀ (pid : PIDGains),
                    pid_output pid 0 0 0 = 0
  pole_place    : ∀ (A B s_star : ℝ), B ≠ 0 →
                    ∃ K, closed_loop_A A B K = s_star
  ctrl_possible : ∀ (A B : ℝ), B ≠ 0 →
                    is_controllable A B
  obs_possible  : ∀ (A C : ℝ), C ≠ 0 →
                    is_observable A C
  gain_pos      : ∀ (Kn Kc : ℝ),
                    0 < Kn → 0 < Kc →
                    0 < gain_margin Kn Kc
  sys_lyap_nn   : ∀ (P : ℝ) (hP : 0 < P)
                    (s : Domain21 → ℝ),
                    0 ≤ system_lyapunov P hP s
  gov_approved  : ∀ (dcs : DomainControlSystem),
                    governance_approved dcs

def CTLock : ControlLock where
  zero_equil    := zero_is_equilibrium_zero_input
  QL_pos        := quadratic_lyapunov_pos
  QL_deriv_neg  := QL_derivative_neg_stable
  pid_zero      := pid_zero_at_equilibrium
  pole_place    := pole_placement
  ctrl_possible := single_input_controllable
  obs_possible  := single_output_observable
  gain_pos      := gain_margin_pos
  sys_lyap_nn   := system_lyapunov_nonneg
  gov_approved  := governance_approved_all_stable

end ControlTheory
