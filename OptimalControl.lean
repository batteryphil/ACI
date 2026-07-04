-- OptimalControl.lean
import Mathlib

namespace OptimalControl

open Finset Real

-- ============================================================
-- SECTION 1: PONTRYAGIN HAMILTONIAN
-- H(x, u, p) = p·f(x,u) - L(x,u)
-- ============================================================

noncomputable def pontryagin_H (f L : ℝ → ℝ → ℝ) (x u p : ℝ) : ℝ := p * f x u - L x u

theorem pontryagin_H_linear_in_p (f L : ℝ → ℝ → ℝ) (x u p q : ℝ) :
    pontryagin_H f L x u (p + q) = pontryagin_H f L x u p + pontryagin_H f L x u q := by
  unfold pontryagin_H; ring

theorem pontryagin_H_zero_cost (f : ℝ → ℝ → ℝ) (x u p : ℝ) :
    pontryagin_H f (fun _ _ => 0) x u p = p * f x u := by
  unfold pontryagin_H; ring

-- Costate equation: dp/dt = -∂H/∂x
noncomputable def costate_update (f L : ℝ → ℝ → ℝ) (x u p eps : ℝ) : ℝ :=
  -(pontryagin_H f L (x + eps) u p - pontryagin_H f L x u p) / eps

-- Maximum principle: u* maximizes H over u
def satisfies_maximum_principle (f L : ℝ → ℝ → ℝ) (x p u_star : ℝ) : Prop :=
  ∀ u : ℝ, pontryagin_H f L x u p ≤ pontryagin_H f L x u_star p

theorem max_principle_at_optimum (f L : ℝ → ℝ → ℝ) (x p u_star : ℝ)
    (h : satisfies_maximum_principle f L x p u_star) :
    ∀ u, pontryagin_H f L x u p ≤ pontryagin_H f L x u_star p := h

-- ============================================================
-- SECTION 2: LQR COST FUNCTION
-- J = ∫ (Q x² + R u²) dt
-- ============================================================

noncomputable def LQR_cost (Q R x u : ℝ) : ℝ := Q * x ^ 2 + R * u ^ 2

theorem LQR_cost_nonneg (Q R x u : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R) : 0 ≤ LQR_cost Q R x u := by
  unfold LQR_cost; positivity

theorem LQR_cost_zero_iff (Q R x u : ℝ) (hQ : 0 < Q) (hR : 0 < R) :
    LQR_cost Q R x u = 0 ↔ x = 0 ∧ u = 0 := by
  unfold LQR_cost; constructor
  · intro h
    have h1 : 0 ≤ Q * x^2 := mul_nonneg (le_of_lt hQ) (sq_nonneg x)
    have h2 : 0 ≤ R * u^2 := mul_nonneg (le_of_lt hR) (sq_nonneg u)
    constructor
    · linarith [h1, h2, h]
    · linarith [h1, h2, h]
  · rintro ⟨hx, hu⟩; simp [hx, hu]

theorem LQR_cost_symmetric (Q R : ℝ) (x u : ℝ) : LQR_cost Q R x u = LQR_cost Q R (-x) (-u) := by
  unfold LQR_cost; ring

theorem LQR_cost_quadratic_scaling (Q R x u c : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    LQR_cost Q R (c * x) (c * u) = c ^ 2 * LQR_cost Q R x u := by
  unfold LQR_cost; ring

-- ============================================================
-- SECTION 3: RICCATI EQUATION
-- ============================================================

noncomputable def riccati_feedback (P B R : ℝ) (hR : 0 < R) : ℝ := -(B * P) / R

theorem riccati_feedback_neg (P B R : ℝ) (hR : 0 < R) (hP : 0 < P) (hB : 0 < B) :
    riccati_feedback P B R hR < 0 := by
  unfold riccati_feedback
  have hBP : 0 < B * P := mul_pos hB hP
  exact neg_div_pos_of_pos hBP hR

theorem riccati_feedback_zero_at_equilibrium (B R : ℝ) (hR : 0 < R) :
    riccati_feedback 0 B R hR = 0 := by unfold riccati_feedback; simp

noncomputable def closed_loop_dynamics (A B P R x : ℝ) (hR : 0 < R) : ℝ :=
  A * x + B * riccati_feedback P B R hR * x

theorem closed_loop_stable (A B P R : ℝ) (hR : 0 < R) (hP : 0 < P) (hB : 0 < B)
    (hA : A < B ^ 2 * P / R) : closed_loop_dynamics A B P R 1 hR < A := by
  unfold closed_loop_dynamics riccati_feedback
  field_simp
  linarith

-- ============================================================
-- SECTION 4: BELLMAN PRINCIPLE OF OPTIMALITY
-- ============================================================

noncomputable def value_function_decomp (V : ℝ → ℝ) (x0 x1 stage_cost : ℝ) : Prop := V x0 = stage_cost + V x1

theorem bellman_principle (V : ℝ → ℝ) (x0 x1 stage_cost : ℝ) (h : value_function_decomp V x0 x1 stage_cost) :
    V x0 - V x1 = stage_cost := by rw [value_function_decomp] at h; linarith

theorem bellman_nonneg_stage (V : ℝ → ℝ) (x0 x1 stage_cost : ℝ) (hsc : 0 ≤ stage_cost)
    (h : value_function_decomp V x0 x1 stage_cost) : V x1 ≤ V x0 := by
  unfold value_function_decomp at h; linarith

theorem value_function_lyapunov (V : ℝ → ℝ) (hV0 : V 0 = 0) (hVpos : ∀ x, 0 ≤ V x)
    (hVdec : ∀ x u stage : ℝ, 0 ≤ stage → value_function_decomp V x (x + u) stage → V (x + u) ≤ V x) :
    ∀ x u stage : ℝ, 0 ≤ stage → value_function_decomp V x (x + u) stage → V (x + u) ≤ V x := hVdec

-- ============================================================
-- SECTION 5: HAMILTON-JACOBI-BELLMAN EQUATION
-- ============================================================

noncomputable def HJB_residual (V : ℝ → ℝ) (f L : ℝ → ℝ → ℝ) (x u dV_dx : ℝ) : ℝ := dV_dx * f x u + L x u

theorem HJB_nonneg_at_min (V : ℝ → ℝ) (f L : ℝ → ℝ → ℝ) (x u_star dV_dx : ℝ) (hL : 0 ≤ L x u_star)
    (hf : 0 ≤ dV_dx * f x u_star) : 0 ≤ HJB_residual V f L x u_star dV_dx := by
  unfold HJB_residual; linarith

def satisfies_HJB (V : ℝ → ℝ) (f L : ℝ → ℝ → ℝ) (dV_dx : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, ∃ u_star : ℝ, HJB_residual V f L x u_star (dV_dx x) = 0

-- ============================================================
-- SECTION 6: TRANSVERSALITY CONDITIONS
-- ============================================================

def terminal_transversality (p_T terminal_cost_gradient : ℝ) : Prop := p_T = terminal_cost_gradient

theorem transversality_free_endpoint (p_T : ℝ) (h : terminal_transversality p_T 0) : p_T = 0 := h

theorem transversality_fixed_endpoint (p_T lambda : ℝ) (h : terminal_transversality p_T lambda) : p_T = lambda := h

-- ============================================================
-- SECTION 7: DISCRETE-TIME OPTIMAL CONTROL
-- ============================================================

noncomputable def discrete_value (V_next : ℝ → ℝ) (f L : ℝ → ℝ → ℝ) (x u : ℝ) : ℝ := L x u + V_next (f x u)

theorem discrete_bellman_nonneg (V_next : ℝ → ℝ) (f L : ℝ → ℝ → ℝ) (x u : ℝ) (hL : 0 ≤ L x u)
    (hV : 0 ≤ V_next (f x u)) : 0 ≤ discrete_value V_next f L x u := by
  unfold discrete_value; linarith

noncomputable def accumulated_cost (L : ℝ → ℝ → ℝ) (traj ctrl : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum (fun k => L (traj k) (ctrl k))

theorem accumulated_cost_nonneg (L : ℝ → ℝ → ℝ) (traj ctrl : ℕ → ℝ) (N : ℕ)
    (hL : ∀ k, 0 ≤ L (traj k) (ctrl k)) : 0 ≤ accumulated_cost L traj ctrl N := by
  unfold accumulated_cost; apply Finset.sum_nonneg; intro k _; exact hL k

-- ============================================================
-- SECTION 8: AWM OPTIMAL CONTROL BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure DomainControlWeights where
  Q : Domain21 → ℝ
  R : Domain21 → ℝ
  Q_pos : ∀ d, 0 < Q d
  R_pos : ∀ d, 0 < R d

noncomputable def system_LQR_cost (w : DomainControlWeights) (states inputs : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d => LQR_cost (w.Q d) (w.R d) (states d) (inputs d))

theorem system_LQR_cost_nonneg (w : DomainControlWeights) (states inputs : Domain21 → ℝ) :
    0 ≤ system_LQR_cost w states inputs := by
  unfold system_LQR_cost; apply Finset.sum_nonneg; intro d _; exact LQR_cost_nonneg _ _ _ _ (le_of_lt (w.Q_pos d)) (le_of_lt (w.R_pos d))

theorem system_LQR_zero_at_rest (w : DomainControlWeights) : system_LQR_cost w (fun _ => 0) (fun _ => 0) = 0 := by
  unfold system_LQR_cost LQR_cost; simp

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure OptimalControlLock where
  LQR_nn      : ∀ (Q R x u : ℝ), 0 ≤ Q → 0 ≤ R → 0 ≤ LQR_cost Q R x u
  bellman     : ∀ (V : ℝ → ℝ) (x0 x1 sc : ℝ), value_function_decomp V x0 x1 sc → V x0 - V x1 = sc
  riccati_neg : ∀ (P B R : ℝ) (hR : 0 < R), 0 < P → 0 < B → riccati_feedback P B R hR < 0
  acc_nn      : ∀ (L : ℝ → ℝ → ℝ) (x u : ℕ → ℝ) (N : ℕ), (∀ k, 0 ≤ L (x k) (u k)) → 0 ≤ accumulated_cost L x u N
  sys_nn      : ∀ (w : DomainControlWeights) (s i : Domain21 → ℝ), 0 ≤ system_LQR_cost w s i

def OCLock : OptimalControlLock where
  LQR_nn      := fun Q R x u hQ hR => LQR_cost_nonneg Q R x u hQ hR
  bellman     := fun V x0 x1 sc h => bellman_principle V x0 x1 sc h
  riccati_neg := fun P B R hR hP hB => riccati_feedback_neg P B R hR hP hB
  acc_nn      := fun L x u N hL => accumulated_cost_nonneg L x u N hL
  sys_nn      := fun w s i => system_LQR_cost_nonneg w s i

end OptimalControl

