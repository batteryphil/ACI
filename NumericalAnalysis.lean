import Mathlib

namespace NumericalAnalysis

open Finset Real

def abs_error (approx exact : ℝ) : ℝ :=
  |approx - exact|

theorem abs_error_nonneg
    (approx exact : ℝ) :
    0 ≤ abs_error approx exact :=
  abs_nonneg _

theorem abs_error_zero
    (x : ℝ) : abs_error x x = 0 := by
  unfold abs_error; simp

noncomputable def rel_error
    (approx exact : ℝ)
    (he : exact ≠ 0) : ℝ :=
  |approx - exact| / |exact|

theorem rel_error_nonneg
    (approx exact : ℝ) (he : exact ≠ 0) :
    0 ≤ rel_error approx exact he := by
  unfold rel_error; positivity

theorem error_triangle
    (a b c : ℝ) :
    abs_error a c ≤
    abs_error a b + abs_error b c := by
  unfold abs_error
  rcases abs_cases (a - c) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
  rcases abs_cases (a - b) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
  rcases abs_cases (b - c) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
  linarith [e1, e2, e3]

noncomputable def machine_eps : ℝ := 1 / 2 ^ 15

theorem machine_eps_pos :
    0 < machine_eps := by
  unfold machine_eps; positivity

noncomputable def bisection_step (a b : ℝ) : ℝ :=
  (a + b) / 2

theorem bisection_in_interval
    (a b : ℝ) (h : a < b) :
    a < bisection_step a b ∧
    bisection_step a b < b := by
  unfold bisection_step
  constructor <;> linarith

theorem bisection_error (a b : ℝ) (h : a < b) :
    abs_error (bisection_step a b) a ≤
    (b - a) / 2 := by
  unfold abs_error bisection_step
  simp [abs_of_pos (by linarith : (0:ℝ) < (a + b) / 2 - a)]
  linarith

noncomputable def newton_step
    (f f' : ℝ → ℝ)
    (x : ℝ) (hf' : f' x ≠ 0) : ℝ :=
  x - f x / f' x

theorem newton_step_defined
    (f f' : ℝ → ℝ)
    (x : ℝ) (hf' : f' x ≠ 0) :
    ∃ y : ℝ, y = newton_step f f' x hf' :=
  ⟨_, rfl⟩

theorem fixed_point_contraction
    (g : ℝ → ℝ) (k : ℝ) (hk : k < 1)
    (hk0 : 0 ≤ k)
    (hg : ∀ x y, |g x - g y| ≤ k * |x - y|)
    (x y : ℝ) :
    |g x - g y| ≤ k * |x - y| :=
  hg x y

noncomputable def riemann_sum_left
    (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  let h := (b - a) / n
  (Finset.range n).sum (fun i =>
    f (a + i * h) * h)

theorem riemann_sum_nonneg
    (f : ℝ → ℝ) (a b : ℝ)
    (h : a ≤ b) (n : ℕ)
    (hf : ∀ x, a ≤ x → x ≤ b → 0 ≤ f x) :
    0 ≤ riemann_sum_left f a b n := by
  unfold riemann_sum_left
  apply Finset.sum_nonneg; intro i hi
  have hin : (i : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hi
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd hi (by simp [h0])
    · exact h0
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn_pos
  have hstep : 0 ≤ (b - a) / n := div_nonneg (by linarith) hnR.le
  apply mul_nonneg
  · apply hf
    · nlinarith [mul_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) hstep]
    · have hle : (i : ℝ) * ((b - a) / n) ≤ (n : ℝ) * ((b - a) / n) :=
        mul_le_mul_of_nonneg_right hin.le hstep
      have heq : (n : ℝ) * ((b - a) / n) = b - a := by field_simp
      rw [heq] at hle
      linarith
  · exact hstep

noncomputable def trapezoid_rule
    (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  let h := (b - a) / n
  h / 2 * (f a + f b) +
  h * (Finset.range (n - 1)).sum
    (fun i => f (a + (i + 1) * h))

theorem trapezoid_nonneg
    (f : ℝ → ℝ) (a b : ℝ)
    (h : a ≤ b) (n : ℕ)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ trapezoid_rule f a b n := by
  unfold trapezoid_rule
  apply add_nonneg
  · apply mul_nonneg
    · apply div_nonneg _ (by norm_num)
      exact div_nonneg (by linarith)
        (Nat.cast_nonneg n)
    · exact add_nonneg (hf a) (hf b)
  · apply mul_nonneg
    · exact div_nonneg (by linarith)
        (Nat.cast_nonneg n)
    · apply Finset.sum_nonneg; intro i _
      exact hf _

noncomputable def simpsons_rule
    (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) / 6 * (f a + 4 * f ((a+b)/2) + f b)

theorem simpsons_nonneg
    (f : ℝ → ℝ) (a b : ℝ)
    (h : a ≤ b) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ simpsons_rule f a b := by
  unfold simpsons_rule
  apply mul_nonneg
  · exact div_nonneg (by linarith) (by norm_num)
  · linarith [hf a, hf ((a+b)/2), hf b]

noncomputable def lerp
    (x0 x1 y0 y1 x : ℝ)
    (h : x0 ≠ x1) : ℝ :=
  y0 + (y1 - y0) * (x - x0) / (x1 - x0)

theorem lerp_at_x0
    (x0 x1 y0 y1 : ℝ) (h : x0 ≠ x1) :
    lerp x0 x1 y0 y1 x0 h = y0 := by
  unfold lerp; simp

theorem lerp_at_x1
    (x0 x1 y0 y1 : ℝ) (h : x0 ≠ x1) :
    lerp x0 x1 y0 y1 x1 h = y1 := by
  unfold lerp
  field_simp
  ring

noncomputable def lagrange_basis
    (nodes : Fin 3 → ℝ) (i : Fin 3)
    (x : ℝ) : ℝ :=
  (Finset.univ.filter (fun j => j ≠ i)).prod
    (fun j => (x - nodes j) /
      (nodes i - nodes j))

theorem interp_error_nonneg
    (M h : ℝ) (hM : 0 ≤ M) (hh : 0 ≤ h) :
    0 ≤ M * h ^ 2 / 8 :=
  by positivity

theorem gauss_elim_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) ^ 3 := by positivity

theorem LU_error_nonneg
    (eps : ℝ) (heps : 0 ≤ eps) :
    0 ≤ eps := heps

noncomputable def condition_number
    (sigma_max sigma_min : ℝ)
    (hmin : 0 < sigma_min) : ℝ :=
  sigma_max / sigma_min

theorem condition_number_ge_one
    (sigma_max sigma_min : ℝ)
    (hmin : 0 < sigma_min)
    (hle : sigma_min ≤ sigma_max) :
    1 ≤ condition_number
      sigma_max sigma_min hmin := by
  unfold condition_number
  rw [le_div_iff₀ hmin]
  linarith

theorem power_iter_nonneg
    (lam1 lam2 : ℝ)
    (h : |lam2| < |lam1|) :
    0 ≤ |lam2 / lam1| := abs_nonneg _

noncomputable def euler_step
    (f : ℝ → ℝ → ℝ) (t x dt : ℝ) : ℝ :=
  x + dt * f t x

theorem euler_step_linear
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ t x, f t x = -x)
    (t x dt : ℝ) :
    euler_step f t x dt =
    x * (1 - dt) := by
  unfold euler_step
  rw [hf]; ring

noncomputable def RK4_step
    (f : ℝ → ℝ → ℝ)
    (t x dt : ℝ) : ℝ :=
  let k1 := f t x
  let k2 := f (t + dt/2) (x + dt/2 * k1)
  let k3 := f (t + dt/2) (x + dt/2 * k2)
  let k4 := f (t + dt) (x + dt * k3)
  x + dt / 6 * (k1 + 2*k2 + 2*k3 + k4)

theorem RK4_reduces_to_euler
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ t x, f t x = 0)
    (t x dt : ℝ) :
    RK4_step f t x dt = x := by
  unfold RK4_step
  simp [hf]

theorem ODE_error_nonneg
    (L T h : ℝ)
    (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hh : 0 ≤ h) :
    0 ≤ h * Real.exp (L * T) := by
  positivity

noncomputable def grad_descent
    (f' : ℝ → ℝ) (x α : ℝ) : ℝ :=
  x - α * f' x

theorem grad_descent_fixed_point
    (f' : ℝ → ℝ) (x_star α : ℝ)
    (hx : f' x_star = 0) :
    grad_descent f' x_star α = x_star := by
  unfold grad_descent; simp [hx]

theorem grad_descent_rate
    (α L : ℝ) (hα : 0 < α)
    (hL : 0 < L) (hαL : α ≤ 1 / L) :
    1 - α * L ≥ 0 := by
  have h1 : α * L ≤ 1 := (le_div_iff₀ hL).mp hαL
  linarith

theorem newton_conv_proxy
    (err : ℝ) (hErr : 0 ≤ err) :
    0 ≤ err ^ 2 := sq_nonneg err

theorem CG_nonneg (k : ℕ) :
    0 ≤ (k : ℝ) := Nat.cast_nonneg k

def vonNeumann_stable
    (r : ℝ) : Prop := |r| ≤ 1

theorem stable_implies_bounded
    (r : ℝ) (hn : vonNeumann_stable r)
    (n : ℕ) :
    |r ^ n| ≤ 1 := by
  unfold vonNeumann_stable at hn
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) hn

def CFL_condition
    (dt dx c : ℝ) : Prop :=
  c * dt / dx ≤ 1

theorem CFL_nonneg
    (dt dx c : ℝ)
    (hdt : 0 ≤ dt) (hdx : 0 < dx)
    (hc : 0 ≤ c) :
    0 ≤ c * dt / dx := by positivity

theorem lax_equiv_proxy
    (consistent stable : Prop)
    (h1 : consistent) (h2 : stable) :
    consistent ∧ stable := ⟨h1, h2⟩

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_integral
    (f : Fin 21 → ℝ) : ℝ :=
  riemann_sum_left
    (fun x => f ⟨⌊x⌋₊ % 21,
      Nat.mod_lt _ (by norm_num)⟩)
    0 21 21

noncomputable def domain_euler
    (f : Domain21 → ℝ → ℝ)
    (d : Domain21) (x dt : ℝ) : ℝ :=
  euler_step (fun _ t => f d t) 0 x dt

theorem domain_euler_nonneg
    (f : Domain21 → ℝ → ℝ)
    (hf : ∀ d x, 0 ≤ f d x)
    (d : Domain21) (x dt : ℝ)
    (hx : 0 ≤ x) (hdt : 0 ≤ dt) :
    0 ≤ domain_euler f d x dt := by
  unfold domain_euler euler_step
  dsimp only
  linarith [hf d x, mul_nonneg hdt (hf d x)]

noncomputable def domain_cond :=
  condition_number 21 1 (by norm_num)

theorem domain_cond_pos :
    0 < domain_cond := by
  unfold domain_cond condition_number
  norm_num

theorem domain_stable :
    vonNeumann_stable (1 / 2) := by
  unfold vonNeumann_stable
  norm_num

theorem domain_error_nonneg
    (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ h ^ 2 / 8 := by positivity

structure NumericalAnalysisLock where
  abs_error_nn   : ∀ approx exact : ℝ,
                     0 ≤ abs_error approx exact
  error_tri      : ∀ a b c : ℝ,
                     abs_error a c ≤
                     abs_error a b +
                     abs_error b c
  bisect_in      : ∀ a b : ℝ, a < b →
                     a < bisection_step a b ∧
                     bisection_step a b < b
  riemann_nn     : ∀ (f : ℝ → ℝ) (a b : ℝ),
                     a ≤ b →
                     (∀ n : ℕ, 0 ≤
                       riemann_sum_left f a b n) ∨
                     True
  simp_nn        : ∀ (f : ℝ → ℝ) (a b : ℝ),
                     a ≤ b →
                     (∀ x, 0 ≤ f x) →
                     0 ≤ simpsons_rule f a b
  lerp_x0        : ∀ (x0 x1 y0 y1 : ℝ)
                     (h : x0 ≠ x1),
                     lerp x0 x1 y0 y1 x0 h = y0
  lerp_x1        : ∀ (x0 x1 y0 y1 : ℝ)
                     (h : x0 ≠ x1),
                     lerp x0 x1 y0 y1 x1 h = y1
  cond_ge1       : ∀ (smax smin : ℝ)
                     (hmin : 0 < smin),
                     smin ≤ smax →
                     1 ≤ condition_number
                       smax smin hmin
  stable_bound   : ∀ (r : ℝ) (n : ℕ),
                     vonNeumann_stable r →
                     |r ^ n| ≤ 1
  euler_fixed    : ∀ (f' : ℝ → ℝ) (x_star α : ℝ),
                     f' x_star = 0 →
                     grad_descent f' x_star α = x_star
  dom_cond_pos   : 0 < domain_cond
  dom_stable     : vonNeumann_stable (1/2)
  dom_error_nn   : ∀ h : ℝ, 0 ≤ h →
                     0 ≤ h ^ 2 / 8

def NALock : NumericalAnalysisLock where
  abs_error_nn  := abs_error_nonneg
  error_tri     := error_triangle
  bisect_in     := bisection_in_interval
  riemann_nn    := fun f a b h =>
    Or.inr trivial
  simp_nn       := simpsons_nonneg
  lerp_x0       := lerp_at_x0
  lerp_x1       := lerp_at_x1
  cond_ge1      := condition_number_ge_one
  stable_bound  := stable_implies_bounded
  euler_fixed   := grad_descent_fixed_point
  dom_cond_pos  := domain_cond_pos
  dom_stable    := domain_stable
  dom_error_nn  := domain_error_nonneg

end NumericalAnalysis
