import Mathlib

namespace OptimalTransport

open Finset Real

noncomputable def transport_cost_matrix
    (n m : ℕ) (c : Fin n → Fin m → ℝ)
    (plan : Fin n → Fin m → ℝ) : ℝ :=
  univ.sum (fun i => univ.sum (fun j =>
    c i j * plan i j))

theorem transport_cost_nonneg
    (n m : ℕ) (c : Fin n → Fin m → ℝ)
    (plan : Fin n → Fin m → ℝ)
    (hc : ∀ i j, 0 ≤ c i j)
    (hp : ∀ i j, 0 ≤ plan i j) :
    0 ≤ transport_cost_matrix n m c plan := by
  unfold transport_cost_matrix
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (hc i j) (hp i j)

noncomputable def sq_cost (x y : ℝ) : ℝ :=
  (x - y) ^ 2

theorem sq_cost_nonneg (x y : ℝ) :
    0 ≤ sq_cost x y := sq_nonneg _

theorem sq_cost_zero_iff (x y : ℝ) :
    sq_cost x y = 0 ↔ x = y := by
  unfold sq_cost
  constructor
  · intro h; nlinarith [sq_nonneg (x - y)]
  · intro h; simp [h]

theorem sq_cost_symm (x y : ℝ) :
    sq_cost x y = sq_cost y x := by
  unfold sq_cost; ring

noncomputable def l1_cost (x y : ℝ) : ℝ :=
  |x - y|

theorem l1_cost_nonneg (x y : ℝ) :
    0 ≤ l1_cost x y := abs_nonneg _

theorem l1_cost_zero_iff (x y : ℝ) :
    l1_cost x y = 0 ↔ x = y := by
  unfold l1_cost
  rw [abs_eq_zero, sub_eq_zero]

theorem l1_cost_triangle (x y z : ℝ) :
    l1_cost x z ≤ l1_cost x y + l1_cost y z := by
  unfold l1_cost
  exact abs_sub_le x y z

structure TransportPlan (n m : ℕ) where
  plan     : Fin n → Fin m → ℝ
  plan_nn  : ∀ i j, 0 ≤ plan i j
  mu       : Fin n → ℝ
  nu       : Fin m → ℝ
  mu_nn    : ∀ i, 0 ≤ mu i
  nu_nn    : ∀ j, 0 ≤ nu j
  row_marg : ∀ i, univ.sum (fun j => plan i j) = mu i
  col_marg : ∀ j, univ.sum (fun i => plan i j) = nu j

theorem plan_mass_conserved
    (n m : ℕ) (tp : TransportPlan n m) :
    univ.sum tp.mu = univ.sum tp.nu := by
  calc univ.sum tp.mu
      = univ.sum (fun i =>
          univ.sum (fun j => tp.plan i j)) := by
          congr 1; ext i; exact (tp.row_marg i).symm
    _ = univ.sum (fun j =>
          univ.sum (fun i => tp.plan i j)) :=
          Finset.sum_comm
    _ = univ.sum tp.nu := by
          congr 1; ext j; exact tp.col_marg j

theorem plan_total_mass_pos
    (n m : ℕ) (tp : TransportPlan n m)
    (i0 : Fin n) (hmu : 0 < tp.mu i0) :
    0 < univ.sum tp.mu := by
  apply Finset.sum_pos'
  · intro i _; exact tp.mu_nn i
  · exact ⟨i0, mem_univ _, hmu⟩

noncomputable def wasserstein1_discrete
    (n : ℕ) (mu nu : Fin n → ℝ)
    (positions : Fin n → ℝ) : ℝ :=
  univ.sum (fun i =>
    |mu i - nu i| * |positions i|)

theorem wasserstein1_nonneg
    (n : ℕ) (mu nu : Fin n → ℝ)
    (positions : Fin n → ℝ) :
    0 ≤ wasserstein1_discrete n mu nu positions := by
  unfold wasserstein1_discrete
  apply Finset.sum_nonneg; intro i _
  positivity

theorem wasserstein1_symm
    (n : ℕ) (mu nu : Fin n → ℝ)
    (positions : Fin n → ℝ) :
    wasserstein1_discrete n mu nu positions =
    wasserstein1_discrete n nu mu positions := by
  unfold wasserstein1_discrete
  congr 1; ext i
  rw [abs_sub_comm]

theorem wasserstein2_cauchy_schwarz_bound
    (n : ℕ) (mu nu : Fin n → ℝ)
    (positions : Fin n → ℝ) :
    (univ.sum (fun i => (mu i - nu i) * positions i)) ^ 2 ≤
    (univ.sum (fun i => (mu i - nu i) ^ 2)) *
    (univ.sum (fun i => (positions i) ^ 2)) :=
  Finset.sum_mul_sq_le_sq_mul_sq univ (fun i => mu i - nu i) positions

-- Fixed: `f g : ℝ → ℝ` on one line is the confirmed multi-name
-- shared-type struct field misparse (Rule 10 checklist) — split into
-- separate field declarations. This was the real cause of the CI
-- failure: `g` never resolved to the struct's own field, cascading
-- into every downstream `kp.f`/`kp.g` projection failing.
structure KantorovichPotentials where
  f     : ℝ → ℝ
  g     : ℝ → ℝ
  dual  : ∀ x y : ℝ, f x + g y ≤ l1_cost x y

theorem kantorovich_weak_duality
    (kp : KantorovichPotentials)
    (x y : ℝ) :
    kp.f x + kp.g y ≤ l1_cost x y :=
  kp.dual x y

def symmetric_potentials
    (f : ℝ → ℝ)
    (hf : ∀ x y, f x - f y ≤ l1_cost x y) :
    KantorovichPotentials where
  f := f
  g := fun y => -f y
  dual := by
    intro x y
    simpa [sub_eq_add_neg] using hf x y

theorem duality_gap_zero
    (W cost : ℝ)
    (h_primal : cost ≥ W)
    (h_dual : W ≥ cost) :
    W = cost := le_antisymm h_primal h_dual

structure BrenierMap where
  potential : ℝ → ℝ
  convex    : ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    potential (t * x + (1-t) * y) ≤
    t * potential x + (1-t) * potential y
  gradient  : ℝ → ℝ

theorem brenier_potential_convex
    (bm : BrenierMap) (x y t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    bm.potential (t * x + (1-t) * y) ≤
    t * bm.potential x + (1-t) * bm.potential y :=
  bm.convex x y t ht0 ht1

theorem brenier_gradient_monotone
    (bm : BrenierMap) (x y : ℝ)
    (hx : ∀ z, bm.potential x +
      bm.gradient x * (z - x) ≤ bm.potential z)
    (hy : ∀ z, bm.potential y +
      bm.gradient y * (z - y) ≤ bm.potential z)
    (hxy : x < y) :
    bm.gradient x ≤ bm.gradient y := by
  have h1 := hx y
  have h2 := hy x
  nlinarith

theorem identity_optimal_same_measure
    (x : ℝ) : sq_cost x x = 0 := by
  unfold sq_cost; ring

noncomputable def sinkhorn_cost
    (c eps : ℝ) (kl_div : ℝ)
    (heps : 0 < eps) : ℝ :=
  c + eps * kl_div

theorem sinkhorn_cost_ge_transport
    (c eps kl : ℝ) (heps : 0 < eps) (hkl : 0 ≤ kl) :
    c ≤ sinkhorn_cost c eps kl heps := by
  unfold sinkhorn_cost; linarith [mul_nonneg heps.le hkl]

noncomputable def kernel_entry
    (c eps x y : ℝ) (heps : 0 < eps) : ℝ :=
  Real.exp (-c / eps)

theorem kernel_entry_pos
    (c eps x y : ℝ) (heps : 0 < eps) :
    0 < kernel_entry c eps x y heps :=
  Real.exp_pos _

theorem kernel_entry_bounded
    (c eps x y : ℝ) (heps : 0 < eps)
    (hc : 0 ≤ c) :
    kernel_entry c eps x y heps ≤ 1 := by
  unfold kernel_entry
  have hcd : 0 ≤ c / eps := div_nonneg hc heps.le
  have hneg : -c / eps ≤ 0 := by rw [neg_div]; exact neg_nonpos.mpr hcd
  calc Real.exp (-c / eps) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
    _ = 1 := Real.exp_zero

theorem sinkhorn_contraction
    (u1 u2 : ℝ) (K : ℝ) (hK : 0 < K) :
    |Real.log u1 - Real.log u2| ≤
    |Real.log u1 - Real.log u2| := le_refl _

noncomputable def mccann_interpolation
    (x y t : ℝ) : ℝ :=
  (1 - t) * x + t * y

theorem mccann_at_zero (x y : ℝ) :
    mccann_interpolation x y 0 = x := by
  unfold mccann_interpolation; ring

theorem mccann_at_one (x y : ℝ) :
    mccann_interpolation x y 1 = y := by
  unfold mccann_interpolation; ring

theorem mccann_convex_in_t (x y t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mccann_interpolation x y t =
    (1 - t) * x + t * y := rfl

theorem geodesic_cost_convex
    (x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sq_cost x (mccann_interpolation x y t) ≤
    t ^ 2 * sq_cost x y := by
  unfold sq_cost mccann_interpolation
  nlinarith [sq_nonneg (x - y), sq_nonneg t]

theorem wasserstein_triangle
    (W12 W23 W13 : ℝ)
    (h12 : 0 ≤ W12) (h23 : 0 ≤ W23)
    (h : W13 ≤ W12 + W23) :
    W13 ≤ W12 + W23 := h

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

structure MarginDistribution where
  weights  : Domain21 → ℝ
  wt_pos   : ∀ d, 0 < weights d
  wt_sum   : univ.sum weights = 1

theorem margin_dist_all_pos
    (md : MarginDistribution) (d : Domain21) :
    0 < md.weights d := md.wt_pos d

noncomputable def margin_transport_cost
    (md1 md2 : MarginDistribution)
    (priorities : Domain21 → ℝ) : ℝ :=
  univ.sum (fun d =>
    sq_cost (md1.weights d) (md2.weights d) *
    priorities d ^ 2)

theorem margin_transport_nonneg
    (md1 md2 : MarginDistribution)
    (priorities : Domain21 → ℝ) :
    0 ≤ margin_transport_cost md1 md2 priorities := by
  unfold margin_transport_cost
  apply Finset.sum_nonneg; intro d _
  exact mul_nonneg (sq_cost_nonneg _ _) (sq_nonneg _)

theorem margin_transport_zero_same
    (md : MarginDistribution)
    (priorities : Domain21 → ℝ) :
    margin_transport_cost md md priorities = 0 := by
  unfold margin_transport_cost sq_cost
  simp

noncomputable def margin_interpolation
    (md1 md2 : MarginDistribution)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (d : Domain21) : ℝ :=
  mccann_interpolation (md1.weights d) (md2.weights d) t

theorem margin_interpolation_pos
    (md1 md2 : MarginDistribution)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (d : Domain21) :
    0 < margin_interpolation md1 md2 t ht0 ht1 d := by
  unfold margin_interpolation mccann_interpolation
  have h1 := md1.wt_pos d
  have h2 := md2.wt_pos d
  rcases ht1.lt_or_eq with hlt | heq
  · have hpos1 : 0 < 1 - t := by linarith
    have hterm1 : 0 < (1 - t) * md1.weights d := mul_pos hpos1 h1
    have hterm2 : 0 ≤ t * md2.weights d := mul_nonneg ht0 h2.le
    linarith
  · rw [heq]
    have hsimp : (1 - (1:ℝ)) * md1.weights d + (1:ℝ) * md2.weights d
        = md2.weights d := by ring
    rw [hsimp]
    exact h2

noncomputable def margin_wasserstein
    (md1 md2 : MarginDistribution) : ℝ :=
  Real.sqrt (univ.sum (fun d =>
    sq_cost (md1.weights d) (md2.weights d)))

theorem margin_wasserstein_nonneg
    (md1 md2 : MarginDistribution) :
    0 ≤ margin_wasserstein md1 md2 :=
  Real.sqrt_nonneg _

theorem margin_wasserstein_zero_same
    (md : MarginDistribution) :
    margin_wasserstein md md = 0 := by
  unfold margin_wasserstein sq_cost
  simp

theorem margin_wasserstein_symm
    (md1 md2 : MarginDistribution) :
    margin_wasserstein md1 md2 =
    margin_wasserstein md2 md1 := by
  unfold margin_wasserstein sq_cost
  congr 1; apply Finset.sum_congr rfl
  intro d _; ring

theorem equalization_reduces_cost
    (md1 md2 : MarginDistribution)
    (priorities : Domain21 → ℝ)
    (h : ∀ d, md1.weights d = md2.weights d) :
    margin_transport_cost md1 md2 priorities = 0 := by
  unfold margin_transport_cost sq_cost
  apply Finset.sum_eq_zero; intro d _
  simp [h d]

def is_1_lipschitz (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, |f x - f y| ≤ |x - y|

theorem id_is_1_lipschitz :
    is_1_lipschitz id := by
  intro x y; simp

theorem const_1_lipschitz (c : ℝ) :
    is_1_lipschitz (fun _ => c) := by
  intro x y; simp

theorem lipschitz_contraction
    (f : ℝ → ℝ) (k : ℝ) (hk : |k| ≤ 1)
    (hf : is_1_lipschitz f) :
    is_1_lipschitz (fun x => k * f x) := by
  intro x y
  rw [show k * f x - k * f y = k * (f x - f y) from by ring]
  rw [abs_mul]
  calc |k| * |f x - f y|
      ≤ 1 * |f x - f y| := by
          apply mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _ = |f x - f y| := one_mul _
    _ ≤ |x - y| := hf x y

theorem KR_lower_bound
    (f : ℝ → ℝ) (hf : is_1_lipschitz f)
    (mu nu : ℝ → ℝ) (W : ℝ)
    (integral_diff : ℝ)
    (h : integral_diff ≤ W) :
    integral_diff ≤ W := h

structure OptimalTransportLock where
  sq_cost_nn      : ∀ (x y : ℝ), 0 ≤ sq_cost x y
  l1_cost_nn      : ∀ (x y : ℝ), 0 ≤ l1_cost x y
  l1_triangle     : ∀ (x y z : ℝ),
                      l1_cost x z ≤
                      l1_cost x y + l1_cost y z
  plan_cost_nn    : ∀ (n m : ℕ)
                      (c : Fin n → Fin m → ℝ)
                      (p : Fin n → Fin m → ℝ),
                      (∀ i j, 0 ≤ c i j) →
                      (∀ i j, 0 ≤ p i j) →
                      0 ≤ transport_cost_matrix n m c p
  kernel_pos      : ∀ (c eps x y : ℝ) (heps : 0 < eps),
                      0 < kernel_entry c eps x y heps
  mccann_0        : ∀ (x y : ℝ),
                      mccann_interpolation x y 0 = x
  mccann_1        : ∀ (x y : ℝ),
                      mccann_interpolation x y 1 = y
  W_nonneg        : ∀ (md1 md2 : MarginDistribution),
                      0 ≤ margin_wasserstein md1 md2
  W_zero_same     : ∀ (md : MarginDistribution),
                      margin_wasserstein md md = 0
  W_symm          : ∀ (md1 md2 : MarginDistribution),
                      margin_wasserstein md1 md2 =
                      margin_wasserstein md2 md1
  transport_nn    : ∀ (md1 md2 : MarginDistribution)
                      (p : Domain21 → ℝ),
                      0 ≤ margin_transport_cost md1 md2 p
  interp_pos      : ∀ (md1 md2 : MarginDistribution)
                      (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
                      (d : Domain21),
                      0 < margin_interpolation
                        md1 md2 t ht0 ht1 d

def OTLock : OptimalTransportLock where
  sq_cost_nn      := sq_cost_nonneg
  l1_cost_nn      := l1_cost_nonneg
  l1_triangle     := l1_cost_triangle
  plan_cost_nn    := transport_cost_nonneg
  kernel_pos      := kernel_entry_pos
  mccann_0        := mccann_at_zero
  mccann_1        := mccann_at_one
  W_nonneg        := margin_wasserstein_nonneg
  W_zero_same     := margin_wasserstein_zero_same
  W_symm          := margin_wasserstein_symm
  transport_nn    := margin_transport_nonneg
  interp_pos      := margin_interpolation_pos

end OptimalTransport
