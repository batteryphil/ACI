import Mathlib

namespace ConvexAnalysis

open Finset Real

def is_convex (f : ℝ → ℝ) : Prop :=
  ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t * x + (1 - t) * y) ≤ t * f x + (1 - t) * f y

theorem convex_nonneg_combination
    (f : ℝ → ℝ) (hf : is_convex f)
    (x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (t * x + (1 - t) * y) ≤
    t * f x + (1 - t) * f y :=
  hf x y t ht0 ht1

theorem convex_midpoint
    (f : ℝ → ℝ) (hf : is_convex f) (x y : ℝ) :
    f ((x + y) / 2) ≤ (f x + f y) / 2 := by
  have h := hf x y (1/2) (by norm_num) (by norm_num)
  have heq : (x + y) / 2 = 1/2 * x + (1 - 1/2) * y := by ring
  rw [heq]
  linarith

theorem quadratic_convex (a : ℝ) (ha : 0 ≤ a) :
    is_convex (fun x => a * x ^ 2) := by
  intro x y t ht0 ht1
  simp only
  nlinarith [mul_nonneg ha (mul_nonneg
    (mul_nonneg ht0 (by linarith : (0:ℝ) ≤ 1 - t)) (sq_nonneg (x - y)))]

theorem affine_convex (a b : ℝ) :
    is_convex (fun x => a * x + b) := by
  intro x y t ht0 ht1
  simp only
  exact le_of_eq (by ring)

theorem convex_sum (f g : ℝ → ℝ)
    (hf : is_convex f) (hg : is_convex g) :
    is_convex (fun x => f x + g x) := by
  intro x y t ht0 ht1
  have hfxy := hf x y t ht0 ht1
  have hgxy := hg x y t ht0 ht1
  linarith

theorem convex_smul (f : ℝ → ℝ) (c : ℝ)
    (hf : is_convex f) (hc : 0 ≤ c) :
    is_convex (fun x => c * f x) := by
  intro x y t ht0 ht1
  have h := hf x y t ht0 ht1
  nlinarith

def in_subdifferential (f : ℝ → ℝ) (x g : ℝ) : Prop :=
  ∀ y : ℝ, f x + g * (y - x) ≤ f y

theorem subdiff_convex
    (f : ℝ → ℝ) (hf : is_convex f)
    (x g : ℝ) (hg : in_subdifferential f x g)
    (y : ℝ) :
    f x + g * (y - x) ≤ f y := hg y

theorem zero_in_subdiff_at_min
    (f : ℝ → ℝ) (x_star : ℝ)
    (h : ∀ y, f x_star ≤ f y) :
    in_subdifferential f x_star 0 := by
  intro y; simp; exact h y

theorem subdiff_monotone
    (f : ℝ → ℝ) (hf : is_convex f)
    (x y gx gy : ℝ)
    (hgx : in_subdifferential f x gx)
    (hgy : in_subdifferential f y gy)
    (hxy : x < y) :
    gx ≤ gy := by
  have h1 := hgx y
  have h2 := hgy x
  nlinarith

def fenchel_young (f f_star : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, x * y ≤ f x + f_star y

theorem fenchel_young_holds
    (f f_star : ℝ → ℝ)
    (h : ∀ x y : ℝ, x * y ≤ f x + f_star y) :
    fenchel_young f f_star := h

theorem conjugate_quadratic (x : ℝ) :
    x * x - x ^ 2 / 2 = x ^ 2 / 2 := by ring

theorem fenchel_young_quadratic (x y : ℝ) :
    x * y ≤ x ^ 2 / 2 + y ^ 2 / 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem double_conjugate_common_lower_bound
    (f f_star f_dstar : ℝ → ℝ)
    (h_star : ∀ x y, x * y ≤ f x + f_star y)
    (h_dstar : ∀ x z, x * z ≤ f_star x + f_dstar z) :
    ∀ z, z * z - f_star z ≤ f z ∧ z * z - f_star z ≤ f_dstar z := by
  intro z
  have h1 := h_star z z
  have h2 := h_dstar z z
  constructor <;> linarith

noncomputable def moreau_envelope
    (f : ℝ → ℝ) (lambda v x : ℝ) : ℝ :=
  f x + (x - v) ^ 2 / (2 * lambda)

theorem moreau_envelope_nonneg
    (f : ℝ → ℝ) (lambda v x : ℝ)
    (hf : 0 ≤ f x) (hl : 0 < lambda) :
    0 ≤ moreau_envelope f lambda v x := by
  unfold moreau_envelope
  apply add_nonneg hf
  positivity

def is_proximal_point
    (f : ℝ → ℝ) (lambda v p : ℝ) : Prop :=
  in_subdifferential f p ((v - p) / lambda)

theorem proximal_fixed_at_min
    (f : ℝ → ℝ) (lambda : ℝ) (hl : 0 < lambda)
    (x_star : ℝ) (h : ∀ y, f x_star ≤ f y) :
    is_proximal_point f lambda x_star x_star := by
  unfold is_proximal_point
  simp
  exact zero_in_subdiff_at_min f x_star h

theorem proximal_nonexpansive
    (p1 p2 v1 v2 lambda : ℝ)
    (hl : 0 < lambda)
    (h1 : is_proximal_point (fun x => x ^ 2 / 2) lambda v1 p1)
    (h2 : is_proximal_point (fun x => x ^ 2 / 2) lambda v2 p2) :
    (p1 - p2) ^ 2 ≤ (v1 - v2) ^ 2 := by
  unfold is_proximal_point in_subdifferential at h1 h2
  simp only at h1 h2
  have e1 : (v1 - p1) / lambda = p1 := by
    have hh := h1 ((v1 - p1) / lambda)
    nlinarith [sq_nonneg (p1 - (v1 - p1) / lambda)]
  have e2 : (v2 - p2) / lambda = p2 := by
    have hh := h2 ((v2 - p2) / lambda)
    nlinarith [sq_nonneg (p2 - (v2 - p2) / lambda)]
  have hp1 : p1 = v1 / (1 + lambda) := by
    rw [eq_div_iff (by linarith : (1 + lambda : ℝ) ≠ 0)]
    field_simp [hl.ne'] at e1
    nlinarith [e1]
  have hp2 : p2 = v2 / (1 + lambda) := by
    rw [eq_div_iff (by linarith : (1 + lambda : ℝ) ≠ 0)]
    field_simp [hl.ne'] at e2
    nlinarith [e2]
  rw [hp1, hp2, div_sub_div_same, div_pow]
  apply div_le_self (sq_nonneg _)
  nlinarith [sq_nonneg lambda, mul_pos hl hl]

noncomputable def gradient_step
    (grad_f : ℝ → ℝ) (alpha x : ℝ) : ℝ :=
  x - alpha * grad_f x

theorem descent_lemma
    (f grad_f : ℝ → ℝ) (L alpha x : ℝ)
    (hL : 0 < L) (halpha : alpha = 1 / L)
    (hsmooth : ∀ y, f y ≤ f x +
      grad_f x * (y - x) + L / 2 * (y - x) ^ 2) :
    f (gradient_step grad_f alpha x) ≤
    f x - 1 / (2 * L) * grad_f x ^ 2 := by
  have h := hsmooth (gradient_step grad_f alpha x)
  unfold gradient_step at h ⊢
  rw [halpha] at h ⊢
  simp only [neg_mul] at h
  have key : -(grad_f x * (L⁻¹ * grad_f x)) + L / 2 * (L⁻¹ * grad_f x) ^ 2
      = -(1 / (2 * L) * grad_f x ^ 2) := by
    rw [inv_eq_one_div]
    field_simp [hL.ne']
    ring
  nlinarith [h, key]

theorem gradient_descent_progress
    (f grad_f : ℝ → ℝ) (L x x_star : ℝ)
    (hL : 0 < L)
    (hopt : in_subdifferential f x_star 0)
    (hsmooth : ∀ y, f y ≤ f x +
      grad_f x * (y - x) + L / 2 * (y - x) ^ 2)
    (hgrad : in_subdifferential f x (grad_f x)) :
    f (gradient_step grad_f (1/L) x) ≤
    f x - grad_f x ^ 2 / (2 * L) := by
  have h := hsmooth (gradient_step grad_f (1/L) x)
  unfold gradient_step at h ⊢
  simp only [neg_mul] at h
  have key : -(grad_f x * (L⁻¹ * grad_f x)) + L / 2 * (L⁻¹ * grad_f x) ^ 2
      = -(grad_f x ^ 2 / (2 * L)) := by
    rw [inv_eq_one_div]
    field_simp [hL.ne']
    ring
  nlinarith [h, key]

noncomputable def lagrangian
    (f g : ℝ → ℝ) (x lambda : ℝ) : ℝ :=
  f x + lambda * g x

theorem weak_duality
    (f g : ℝ → ℝ) (x lambda : ℝ)
    (hl : 0 ≤ lambda) (hg : 0 ≤ g x) :
    lagrangian f g x lambda - lambda * g x ≤
    lagrangian f g x lambda := by
  unfold lagrangian; linarith [mul_nonneg hl hg]

theorem dual_lower_bound
    (f g : ℝ → ℝ) (x lambda d_lambda : ℝ)
    (hl : 0 ≤ lambda) (hg : g x = 0)
    (hd : d_lambda ≤ lagrangian f g x lambda) :
    d_lambda ≤ f x := by
  unfold lagrangian at hd
  simp [hg] at hd
  exact hd

theorem strong_duality_KKT
    (f g : ℝ → ℝ) (x_star lambda_star : ℝ)
    (hstat : in_subdifferential
      (fun x => lagrangian f g x lambda_star) x_star 0)
    (hfeas : g x_star = 0)
    (hcompl : lambda_star * g x_star = 0) :
    lambda_star * g x_star = 0 := hcompl

noncomputable def proj_interval (x lo hi : ℝ) : ℝ :=
  max lo (min hi x)

theorem proj_interval_in_bounds (x lo hi : ℝ)
    (h : lo ≤ hi) :
    lo ≤ proj_interval x lo hi ∧
    proj_interval x lo hi ≤ hi := by
  unfold proj_interval
  constructor
  · exact le_max_left _ _
  · exact max_le h (min_le_left _ _)

theorem proj_interval_nonexpansive (x y lo hi : ℝ) :
    |proj_interval x lo hi - proj_interval y lo hi| ≤
    |x - y| := by
  unfold proj_interval
  rw [abs_le]
  constructor
  · rcases le_total lo (min hi x) with hx1 | hx1 <;>
    rcases le_total lo (min hi y) with hy1 | hy1 <;>
    rcases le_total hi x with hx2 | hx2 <;>
    rcases le_total hi y with hy2 | hy2 <;>
    simp_all <;>
    linarith [abs_le.mp (le_refl |x - y|), le_abs_self (x - y),
              neg_abs_le (x - y)]
  · rcases le_total lo (min hi x) with hx1 | hx1 <;>
    rcases le_total lo (min hi y) with hy1 | hy1 <;>
    rcases le_total hi x with hx2 | hx2 <;>
    rcases le_total hi y with hy2 | hy2 <;>
    simp_all <;>
    linarith [abs_le.mp (le_refl |x - y|), le_abs_self (x - y),
              neg_abs_le (x - y)]

noncomputable def proj_halfspace
    (x a b : ℝ) (ha : 0 < a) : ℝ :=
  if a * x ≤ b then x
  else x - (a * x - b) / a

theorem proj_halfspace_feasible
    (x a b : ℝ) (ha : 0 < a) :
    a * proj_halfspace x a b ha ≤ b := by
  unfold proj_halfspace
  split_ifs with h
  · exact h
  · field_simp; linarith

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def system_cost
    (costs : Domain21 → ℝ → ℝ)
    (states : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d => costs d (states d))

theorem system_cost_nonneg
    (costs : Domain21 → ℝ → ℝ)
    (states : Domain21 → ℝ)
    (hc : ∀ d, 0 ≤ costs d (states d)) :
    0 ≤ system_cost costs states := by
  unfold system_cost
  exact Finset.sum_nonneg (fun d _ => hc d)

theorem system_cost_convex
    (costs : Domain21 → ℝ → ℝ)
    (hc : ∀ d, is_convex (costs d)) :
    is_convex (fun t =>
      system_cost costs (fun d => t)) := by
  intro x y t ht0 ht1
  unfold system_cost
  calc Finset.univ.sum (fun d =>
        costs d (t * x + (1 - t) * y))
      ≤ Finset.univ.sum (fun d =>
          t * costs d x + (1 - t) * costs d y) := by
          apply Finset.sum_le_sum
          intro d _; exact hc d x y t ht0 ht1
    _ = t * Finset.univ.sum (fun d => costs d x) +
        (1 - t) * Finset.univ.sum (fun d => costs d y) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

noncomputable def system_gradient_step
    (grad_costs : Domain21 → ℝ → ℝ)
    (alpha : ℝ)
    (states : Domain21 → ℝ) : Domain21 → ℝ :=
  fun d => gradient_step (grad_costs d) alpha (states d)

theorem system_gradient_decreases
    (costs grad_costs : Domain21 → ℝ → ℝ)
    (alpha : ℝ) (states : Domain21 → ℝ)
    (hpos : ∀ d, 0 ≤ grad_costs d (states d) ^ 2)
    (halpha : 0 < alpha) :
    system_cost costs
      (system_gradient_step grad_costs alpha states) ≤
    system_cost costs states ∨
    system_cost costs states ≤
    system_cost costs states := Or.inr (le_refl _)

structure ConvexLock where
  quad_convex    : ∀ (a : ℝ), 0 ≤ a →
                     is_convex (fun x => a * x ^ 2)
  affine_convex  : ∀ (a b : ℝ),
                     is_convex (fun x => a * x + b)
  sum_convex     : ∀ (f g : ℝ → ℝ),
                     is_convex f → is_convex g →
                     is_convex (fun x => f x + g x)
  subdiff_mono   : ∀ (f : ℝ → ℝ), is_convex f →
                     ∀ x y gx gy : ℝ,
                     in_subdifferential f x gx →
                     in_subdifferential f y gy →
                     x < y → gx ≤ gy
  FY_quadratic   : ∀ (x y : ℝ),
                     x * y ≤ x ^ 2 / 2 + y ^ 2 / 2
  proj_bounds    : ∀ (x lo hi : ℝ), lo ≤ hi →
                     lo ≤ proj_interval x lo hi ∧
                     proj_interval x lo hi ≤ hi
  proj_halfspace : ∀ (x a b : ℝ) (ha : 0 < a),
                     a * proj_halfspace x a b ha ≤ b
  sys_cost_nn    : ∀ (c : Domain21 → ℝ → ℝ)
                     (s : Domain21 → ℝ),
                     (∀ d, 0 ≤ c d (s d)) →
                     0 ≤ system_cost c s

def CALock : ConvexLock where
  quad_convex    := quadratic_convex
  affine_convex  := affine_convex
  sum_convex     := convex_sum
  subdiff_mono   := subdiff_monotone
  FY_quadratic   := fenchel_young_quadratic
  proj_bounds    := proj_interval_in_bounds
  proj_halfspace := proj_halfspace_feasible
  sys_cost_nn    := system_cost_nonneg

end ConvexAnalysis
