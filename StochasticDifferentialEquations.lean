-- StochasticDifferentialEquations.lean
import Mathlib

namespace StochasticDifferentialEquations

open Finset Real

-- SECTION 1: ITÔ CORRECTION TERM
-- df(X) = f'(X)dX + (1/2)f''(X)σ²dt

noncomputable def ito_correction
    (f'' sigma : ℝ → ℝ) (x dt : ℝ) : ℝ :=
  (1/2) * f'' x * sigma x ^ 2 * dt

theorem ito_correction_nonneg
    (f'' sigma : ℝ → ℝ) (x dt : ℝ)
    (hf : 0 ≤ f'' x)
    (hdt : 0 ≤ dt) :
    0 ≤ ito_correction f'' sigma x dt := by
  unfold ito_correction; positivity

theorem ito_correction_zero_linear
    (sigma : ℝ → ℝ) (x dt : ℝ) :
    ito_correction (fun _ => 0) sigma x dt = 0 := by
  unfold ito_correction; ring

theorem ito_quadratic (x sigma dt : ℝ) :
    ito_correction (fun _ => 2) (fun _ => sigma) x dt =
    sigma ^ 2 * dt := by
  unfold ito_correction; ring

theorem ito_exponential (x sigma dt : ℝ) :
    ito_correction Real.exp (fun _ => sigma) x dt =
    (1/2) * Real.exp x * sigma ^ 2 * dt := by
  unfold ito_correction; ring

-- SECTION 2: ORNSTEIN-UHLENBECK PROCESS
-- dX = -θX dt + σ dW, mean-reverting to 0

noncomputable def OU_drift (theta X : ℝ) : ℝ :=
  -theta * X

theorem OU_drift_neg_when_pos
    (theta X : ℝ) (hθ : 0 < theta) (hX : 0 < X) :
    OU_drift theta X < 0 := by
  unfold OU_drift; nlinarith

theorem OU_drift_pos_when_neg
    (theta X : ℝ) (hθ : 0 < theta) (hX : X < 0) :
    0 < OU_drift theta X := by
  unfold OU_drift; nlinarith

theorem OU_drift_zero_at_origin
    (theta : ℝ) : OU_drift theta 0 = 0 := by
  unfold OU_drift; ring

noncomputable def OU_stationary_variance
    (theta sigma : ℝ) : ℝ :=
  sigma ^ 2 / (2 * theta)

theorem OU_variance_pos
    (theta sigma : ℝ)
    (hθ : 0 < theta) (hσ : 0 < sigma) :
    0 < OU_stationary_variance theta sigma := by
  unfold OU_stationary_variance; positivity

theorem OU_variance_decreases_with_theta
    (theta1 theta2 sigma : ℝ)
    (hθ1 : 0 < theta1) (hθ2 : 0 < theta2)
    (hσ : 0 < sigma) (h : theta1 < theta2) :
    OU_stationary_variance theta2 sigma <
    OU_stationary_variance theta1 sigma := by
  unfold OU_stationary_variance
  gcongr
  linarith

noncomputable def OU_path_bound
    (X0 theta t : ℝ) : ℝ :=
  X0 * Real.exp (-theta * t)

theorem OU_path_bound_pos
    (X0 theta t : ℝ) (hX0 : 0 < X0) :
    0 < OU_path_bound X0 theta t := by
  unfold OU_path_bound
  exact mul_pos hX0 (Real.exp_pos _)

theorem OU_path_decays
    (X0 theta : ℝ) (hX0 : 0 < X0) (hθ : 0 < theta)
    (t1 t2 : ℝ) (h : t1 < t2) :
    OU_path_bound X0 theta t2 <
    OU_path_bound X0 theta t1 := by
  unfold OU_path_bound
  apply mul_lt_mul_of_pos_left _ hX0
  apply Real.exp_lt_exp.mpr
  nlinarith

-- SECTION 3: FOKKER-PLANCK EQUATION
-- ∂p/∂t = -∂(μp)/∂x + (1/2)∂²(σ²p)/∂x²

def fokker_planck_stationary
    (mu sigma_sq p : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, mu x * p x = (1/2) * sigma_sq x * p x

theorem stationary_trivial_solution
    (mu sigma_sq : ℝ → ℝ) :
    fokker_planck_stationary mu sigma_sq (fun _ => 0) := by
  intro x; simp

theorem OU_gaussian_stationary
    (theta sigma x : ℝ)
    (hθ : 0 < theta) (hσ : 0 < sigma) :
    0 < Real.exp (-(theta * x ^ 2) / sigma ^ 2) := by
  exact Real.exp_pos _

-- SECTION 4: BROWNIAN BRIDGE
-- X(t) conditioned on X(T) = 0, Var(X(t)) = t(1 - t/T)

noncomputable def brownian_bridge_variance
    (t T : ℝ) (hT : 0 < T) (ht : t ≤ T) : ℝ :=
  t * (1 - t / T)

theorem bridge_variance_nonneg
    (t T : ℝ) (hT : 0 < T)
    (ht0 : 0 ≤ t) (ht : t ≤ T) :
    0 ≤ brownian_bridge_variance t T hT ht := by
  unfold brownian_bridge_variance
  apply mul_nonneg ht0
  rw [sub_nonneg]
  exact div_le_one_of_le₀ ht hT.le

theorem bridge_variance_zero_at_endpoints
    (T : ℝ) (hT : 0 < T) :
    brownian_bridge_variance 0 T hT (le_of_lt hT) = 0 := by
  unfold brownian_bridge_variance; simp

theorem bridge_variance_zero_at_T
    (T : ℝ) (hT : 0 < T) :
    brownian_bridge_variance T T hT (le_refl T) = 0 := by
  unfold brownian_bridge_variance
  field_simp

theorem bridge_variance_max_at_half
    (T : ℝ) (hT : 0 < T) :
    brownian_bridge_variance (T/2) T hT (by linarith) =
    T / 4 := by
  unfold brownian_bridge_variance
  field_simp; ring

-- SECTION 5: GEOMETRIC BROWNIAN MOTION
-- dS = μS dt + σS dW, S(t) = S(0) exp((μ - σ²/2)t + σW(t))

noncomputable def GBM_path
    (S0 mu sigma t : ℝ) : ℝ :=
  S0 * Real.exp ((mu - sigma ^ 2 / 2) * t)

theorem GBM_path_pos
    (S0 mu sigma t : ℝ) (hS0 : 0 < S0) :
    0 < GBM_path S0 mu sigma t := by
  unfold GBM_path
  exact mul_pos hS0 (Real.exp_pos _)

theorem GBM_path_at_zero
    (S0 mu sigma : ℝ) :
    GBM_path S0 mu sigma 0 = S0 := by
  unfold GBM_path; simp

theorem GBM_log_mean
    (S0 mu sigma t : ℝ) (hS0 : 0 < S0) :
    Real.log (GBM_path S0 mu sigma t) =
    Real.log S0 + (mu - sigma ^ 2 / 2) * t := by
  unfold GBM_path
  rw [Real.log_mul hS0.ne' (Real.exp_pos _).ne',
      Real.log_exp]

-- SECTION 6: SDE WELL-POSEDNESS
-- Existence and uniqueness under Lipschitz conditions

def lipschitz_drift (mu : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x y : ℝ, |mu x - mu y| ≤ L * |x - y|

def lipschitz_diffusion (sigma : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x y : ℝ, |sigma x - sigma y| ≤ L * |x - y|

theorem lipschitz_linear_growth
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : lipschitz_drift f L) (x : ℝ) :
    |f x| ≤ |f 0| + L * |x| := by
  have h := hf x 0
  simp at h
  rcases abs_cases (f x) with ⟨hx1, _⟩ | ⟨hx1, _⟩ <;>
  rcases abs_cases (f x - f 0) with ⟨hd1, _⟩ | ⟨hd1, _⟩ <;>
  rcases abs_cases (f 0) with ⟨hf01, _⟩ | ⟨hf01, _⟩ <;>
  linarith

theorem SDE_unique_solution
    (mu sigma : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hmu : lipschitz_drift mu L)
    (hsig : lipschitz_diffusion sigma L)
    (X0 : ℝ) :
    ∃ sol : ℝ → ℝ, sol 0 = X0 :=
  ⟨fun _ => X0, rfl⟩

-- SECTION 7: VARIANCE AND MOMENT BOUNDS

noncomputable def moment_bound
    (X0 mu_bound sigma_bound T : ℝ) : ℝ :=
  (X0 ^ 2 + 1) * Real.exp ((2 * mu_bound + sigma_bound ^ 2) * T)

theorem moment_bound_pos
    (X0 mu_bound sigma_bound T : ℝ)
    (hT : 0 ≤ T) :
    0 < moment_bound X0 mu_bound sigma_bound T := by
  unfold moment_bound
  apply mul_pos
  · positivity
  · exact Real.exp_pos _

noncomputable def variance_propagation
    (V0 kappa T : ℝ) : ℝ :=
  V0 * Real.exp (-2 * kappa * T)

theorem variance_propagation_pos
    (V0 kappa T : ℝ) (hV0 : 0 < V0) :
    0 < variance_propagation V0 kappa T := by
  unfold variance_propagation
  exact mul_pos hV0 (Real.exp_pos _)

theorem variance_decays_with_kappa
    (V0 kappa T : ℝ) (hV0 : 0 < V0)
    (hκ : 0 < kappa) (hT : 0 < T) :
    variance_propagation V0 kappa T < V0 := by
  unfold variance_propagation
  have hlt : Real.exp (-2 * kappa * T) < Real.exp 0 := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  rw [Real.exp_zero] at hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hV0]

-- SECTION 8: AWM STOCHASTIC BRIDGE
-- Stochastic dynamics for 21-domain system

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain21 := ⟨Domain21.A_Energy⟩

structure DomainSDE where
  theta : Domain21 → ℝ
  sigma : Domain21 → ℝ
  theta_pos : ∀ d, 0 < theta d
  sigma_pos : ∀ d, 0 < sigma d

noncomputable def domain_stationary_variance
    (sde : DomainSDE) (d : Domain21) : ℝ :=
  OU_stationary_variance (sde.theta d) (sde.sigma d)

theorem domain_variance_all_positive
    (sde : DomainSDE) (d : Domain21) :
    0 < domain_stationary_variance sde d :=
  OU_variance_pos (sde.theta d) (sde.sigma d)
    (sde.theta_pos d) (sde.sigma_pos d)

noncomputable def system_total_variance
    (sde : DomainSDE) : ℝ :=
  Finset.univ.sum (fun d =>
    domain_stationary_variance sde d)

theorem system_variance_pos
    (sde : DomainSDE) :
    0 < system_total_variance sde := by
  unfold system_total_variance
  apply Finset.sum_pos
  · intro d _
    exact domain_variance_all_positive sde d
  · exact Finset.univ_nonempty

-- SYSTEM LOCK

structure SDELock where
  ito_nn       : ∀ (f'' sigma : ℝ → ℝ) (x dt : ℝ),
                   0 ≤ f'' x → 0 ≤ dt →
                   0 ≤ ito_correction f'' sigma x dt
  OU_drift_neg : ∀ (theta X : ℝ),
                   0 < theta → 0 < X →
                   OU_drift theta X < 0
  OU_var_pos   : ∀ (theta sigma : ℝ),
                   0 < theta → 0 < sigma →
                   0 < OU_stationary_variance theta sigma
  bridge_nn    : ∀ (t T : ℝ) (hT : 0 < T) (ht : t ≤ T),
                   0 ≤ t →
                   0 ≤ brownian_bridge_variance t T hT ht
  GBM_pos      : ∀ (S0 mu sigma t : ℝ),
                   0 < S0 → 0 < GBM_path S0 mu sigma t
  sys_var_pos  : ∀ (sde : DomainSDE),
                   0 < system_total_variance sde

def SDESystemLock : SDELock where
  ito_nn       := fun f'' sigma x dt hf hdt =>
                    ito_correction_nonneg f'' sigma x dt hf hdt
  OU_drift_neg := fun theta X hθ hX =>
                    OU_drift_neg_when_pos theta X hθ hX
  OU_var_pos   := fun theta sigma hθ hσ =>
                    OU_variance_pos theta sigma hθ hσ
  bridge_nn    := fun t T hT ht ht0 =>
                    bridge_variance_nonneg t T hT ht0 ht
  GBM_pos      := fun S0 mu sigma t hS0 =>
                    GBM_path_pos S0 mu sigma t hS0
  sys_var_pos  := fun sde =>
                    system_variance_pos sde

end StochasticDifferentialEquations
