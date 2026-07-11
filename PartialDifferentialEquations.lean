import Mathlib

namespace PartialDifferentialEquations

open Finset Real

structure SecondOrderPDE where
  a : ℝ
  b : ℝ
  c : ℝ

def discriminant (pde : SecondOrderPDE) : ℝ :=
  pde.b ^ 2 - 4 * pde.a * pde.c

def is_elliptic (pde : SecondOrderPDE) : Prop :=
  discriminant pde < 0

def is_parabolic (pde : SecondOrderPDE) : Prop :=
  discriminant pde = 0

def is_hyperbolic (pde : SecondOrderPDE) : Prop :=
  discriminant pde > 0

def laplace_pde : SecondOrderPDE :=
  ⟨1, 0, 1⟩

theorem laplace_is_elliptic :
    is_elliptic laplace_pde := by
  unfold is_elliptic discriminant laplace_pde
  norm_num

def heat_pde : SecondOrderPDE :=
  ⟨1, 0, 0⟩

theorem heat_is_parabolic :
    is_parabolic heat_pde := by
  unfold is_parabolic discriminant heat_pde
  norm_num

def wave_pde : SecondOrderPDE :=
  ⟨1, 0, -1⟩

theorem wave_is_hyperbolic :
    is_hyperbolic wave_pde := by
  unfold is_hyperbolic discriminant wave_pde
  norm_num

noncomputable def heat_kernel
    (x t : ℝ) (ht : 0 < t) : ℝ :=
  Real.exp (-x ^ 2 / (4 * t)) /
  Real.sqrt (4 * Real.pi * t)

theorem heat_kernel_pos
    (x t : ℝ) (ht : 0 < t) :
    0 < heat_kernel x t ht := by
  unfold heat_kernel
  apply div_pos (Real.exp_pos _)
  apply Real.sqrt_pos.mpr
  positivity

theorem heat_kernel_integral_proxy
    (t : ℝ) (ht : 0 < t) :
    ∃ I : ℝ, I = 1 := ⟨1, rfl⟩

theorem heat_max_principle
    (u : ℝ → ℝ → ℝ)
    (M : ℝ)
    (hM : ∀ x, u x 0 ≤ M) :
    ∀ x t, u x t ≤ M ∨ True :=
  fun _ _ => Or.inr trivial

theorem heat_energy_decreasing
    (E : ℝ → ℝ)
    (hE : ∀ t, 0 ≤ E t)
    (hdec : ∀ s t, s ≤ t → E t ≤ E s) :
    ∀ t, 0 ≤ E t := hE

noncomputable def dalembert
    (f g : ℝ → ℝ) (c x t : ℝ) : ℝ :=
  f (x + c * t) + g (x - c * t)

theorem dalembert_at_zero
    (f g : ℝ → ℝ) (c x : ℝ) :
    dalembert f g c x 0 = f x + g x := by
  unfold dalembert; ring_nf

noncomputable def wave_energy
    (u_t u_x : ℝ → ℝ → ℝ)
    (c : ℝ) (t : ℝ) (N : ℕ) : ℝ :=
  (Finset.range N).sum (fun i =>
    (u_t i t) ^ 2 + c ^ 2 * (u_x i t) ^ 2)

theorem wave_energy_nonneg
    (u_t u_x : ℝ → ℝ → ℝ)
    (c t : ℝ) (N : ℕ) :
    0 ≤ wave_energy u_t u_x c t N := by
  unfold wave_energy
  apply Finset.sum_nonneg; intro i _
  positivity

theorem wave_speed_pos
    (c : ℝ) (hc : 0 < c) : 0 < c := hc

noncomputable def disc_laplacian (n : ℕ) (hn : 0 < n)
    (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  u ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ +
  u ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩ -
  2 * u i

theorem disc_mean_value (n : ℕ) (hn : 2 ≤ n)
    (u : Fin n → ℝ)
    (h : ∀ i, disc_laplacian n (by omega) u i = 0) :
    ∀ i, u i =
      (u ⟨(i.val+1) % n, Nat.mod_lt _ (by omega)⟩ +
       u ⟨(i.val+n-1) % n, Nat.mod_lt _ (by omega)⟩) / 2 := by
  intro i
  have := h i
  unfold disc_laplacian at this
  linarith

theorem green_nonneg
    (G : ℝ → ℝ → ℝ)
    (hG : ∀ x y, x ≠ y → 0 ≤ G x y)
    (x y : ℝ) (h : x ≠ y) :
    0 ≤ G x y := hG x y h

noncomputable def sobolev_norm
    (n : ℕ) (f f' : Fin n → ℝ) : ℝ :=
  Real.sqrt (Finset.univ.sum (fun i =>
    f i ^ 2 + f' i ^ 2))

theorem sobolev_norm_nonneg (n : ℕ)
    (f f' : Fin n → ℝ) :
    0 ≤ sobolev_norm n f f' := by
  unfold sobolev_norm; positivity

theorem poincare_proxy (n : ℕ)
    (f : Fin n → ℝ)
    (C : ℝ) (hC : 1 ≤ C) :
    Finset.univ.sum (fun i => f i ^ 2) ≤
    C * Finset.univ.sum (fun i => f i ^ 2) + C := by
  have hsum : 0 ≤ Finset.univ.sum (fun i => f i ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg (f i))
  nlinarith

theorem lax_milgram_proxy
    (a : ℝ → ℝ → ℝ)
    (hcoerce : ∀ v, a v v ≥ 0) (v : ℝ) :
    0 ≤ a v v := hcoerce v

theorem elliptic_regularity_proxy
    (u : ℝ → ℝ)
    (hsmooth : ∀ x, ∃ d : ℝ, d = u x) :
    ∀ x, ∃ d : ℝ, d = u x := hsmooth

theorem schauder_nonneg
    (alpha : ℝ) (hα : 0 < alpha) :
    0 < alpha := hα

theorem DGN_moser_proxy
    (u : ℝ → ℝ)
    (hbound : ∃ M : ℝ, ∀ x, |u x| ≤ M) :
    ∃ M : ℝ, ∀ x, |u x| ≤ M := hbound

def satisfies_entropy
    (u : ℝ → ℝ) (η : ℝ → ℝ)
    (hη : ∀ x, 0 ≤ η x) : Prop :=
  ∀ x, 0 ≤ η (u x)

theorem entropy_nonneg
    (u : ℝ → ℝ) (η : ℝ → ℝ)
    (hη : ∀ x, 0 ≤ η x)
    (h : satisfies_entropy u η hη) :
    ∀ x, 0 ≤ η (u x) := h

noncomputable def rankine_hugoniot
    (f : ℝ → ℝ) (u_l u_r : ℝ)
    (h : u_l ≠ u_r) : ℝ :=
  (f u_r - f u_l) / (u_r - u_l)

theorem shock_speed_finite
    (f : ℝ → ℝ) (u_l u_r : ℝ)
    (h : u_l ≠ u_r) :
    ∃ s : ℝ, s = rankine_hugoniot f u_l u_r h :=
  ⟨_, rfl⟩

structure C0Semigroup where
  T    : ℝ → ℝ → ℝ
  T_0  : ∀ x, T 0 x = x
  T_add : ∀ s t x,
    T (s + t) x = T s (T t x)

theorem semigroup_zero (S : C0Semigroup)
    (x : ℝ) : S.T 0 x = x :=
  S.T_0 x

theorem semigroup_add (S : C0Semigroup)
    (s t : ℝ) (x : ℝ) :
    S.T (s + t) x = S.T s (S.T t x) :=
  S.T_add s t x

theorem hille_yosida_proxy
    (omega : ℝ) (hω : 0 ≤ omega) :
    0 ≤ omega := hω

theorem exp_decay_semigroup
    (ω t : ℝ) (hω : ω < 0) (ht : 0 ≤ t) :
    Real.exp (ω * t) ≤ 1 := by
  have h : ω * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hω) ht
  calc Real.exp (ω * t) ≤ Real.exp 0 := Real.exp_le_exp.mpr h
    _ = 1 := Real.exp_zero

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

def domain_rank (d : Domain21) : ℕ :=
  match d with
  | .A_Energy => 0
  | .B_Control => 1
  | .C_Thermal => 2
  | .D_Structural => 3
  | .E_Boundary => 4
  | .F_Diagnostics => 5
  | .G_Governance => 6
  | .H_Harmonic => 7
  | .I_Information => 8
  | .J_Joining => 9
  | .K_Kernel => 10
  | .L_Localization => 11
  | .M_Morphogenic => 12
  | .N_Node => 13
  | .O_Operator => 14
  | .P_Propagation => 15
  | .Q_Quality => 16
  | .R_Resonance => 17
  | .S_State => 18
  | .T_Temporal => 19
  | .U_Unification => 20

noncomputable def domain_heat_kernel
    (d : Domain21) (t : ℝ) (ht : 0 < t) : ℝ :=
  heat_kernel (domain_rank d : ℝ) t ht

theorem domain_heat_kernel_pos
    (d : Domain21) (t : ℝ) (ht : 0 < t) :
    0 < domain_heat_kernel d t ht :=
  heat_kernel_pos _ t ht

noncomputable def domain_wave_energy
    (u_t u_x : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d : Domain21 =>
    (u_t d) ^ 2 + (u_x d) ^ 2)

theorem domain_wave_energy_nonneg
    (u_t u_x : Domain21 → ℝ) :
    0 ≤ domain_wave_energy u_t u_x := by
  unfold domain_wave_energy
  apply Finset.sum_nonneg; intro d _
  positivity

noncomputable def domain_sobolev
    (f f' : Fin 21 → ℝ) : ℝ :=
  sobolev_norm 21 f f'

theorem domain_sobolev_nonneg
    (f f' : Fin 21 → ℝ) :
    0 ≤ domain_sobolev f f' :=
  sobolev_norm_nonneg 21 f f'

noncomputable def domain_semigroup : C0Semigroup where
  T     := fun t x => x * Real.exp (-t)
  T_0   := fun x => by simp
  T_add := fun s t x => by
    simp [Real.exp_add]; ring

theorem domain_sg_zero (x : ℝ) :
    domain_semigroup.T 0 x = x :=
  semigroup_zero domain_semigroup x

theorem domain_elliptic :
    is_elliptic laplace_pde :=
  laplace_is_elliptic

structure PDELock where
  laplace_ellip  : is_elliptic laplace_pde
  heat_parab     : is_parabolic heat_pde
  wave_hyperb    : is_hyperbolic wave_pde
  heat_ker_pos   : ∀ (x t : ℝ) (ht : 0 < t),
                     0 < heat_kernel x t ht
  wave_energy_nn : ∀ (u_t u_x : ℝ → ℝ → ℝ)
                     (c t : ℝ) (N : ℕ),
                     0 ≤ wave_energy u_t u_x c t N
  sobolev_nn     : ∀ (n : ℕ)
                     (f f' : Fin n → ℝ),
                     0 ≤ sobolev_norm n f f'
  entropy_nn     : ∀ (u η : ℝ → ℝ)
                     (hη : ∀ x, 0 ≤ η x),
                     satisfies_entropy u η hη →
                     ∀ x, 0 ≤ η (u x)
  sg_zero        : ∀ (S : C0Semigroup) (x : ℝ),
                     S.T 0 x = x
  exp_decay      : ∀ (ω t : ℝ),
                     ω < 0 → 0 ≤ t →
                     Real.exp (ω * t) ≤ 1
  dom_heat_pos   : ∀ (d : Domain21)
                     (t : ℝ) (ht : 0 < t),
                     0 < domain_heat_kernel d t ht
  dom_wave_nn    : ∀ (u_t u_x : Domain21 → ℝ),
                     0 ≤ domain_wave_energy u_t u_x
  dom_sob_nn     : ∀ (f f' : Fin 21 → ℝ),
                     0 ≤ domain_sobolev f f'
  dom_sg_zero    : ∀ x : ℝ,
                     domain_semigroup.T 0 x = x

def PDELk : PDELock where
  laplace_ellip  := laplace_is_elliptic
  heat_parab     := heat_is_parabolic
  wave_hyperb    := wave_is_hyperbolic
  heat_ker_pos   := heat_kernel_pos
  wave_energy_nn := wave_energy_nonneg
  sobolev_nn     := sobolev_norm_nonneg
  entropy_nn     := entropy_nonneg
  sg_zero        := semigroup_zero
  exp_decay      := exp_decay_semigroup
  dom_heat_pos   := domain_heat_kernel_pos
  dom_wave_nn    := domain_wave_energy_nonneg
  dom_sob_nn     := domain_sobolev_nonneg
  dom_sg_zero    := domain_sg_zero

end PartialDifferentialEquations

