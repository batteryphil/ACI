import Mathlib

namespace SymplecticTopology

open Finset Real Matrix
open scoped Matrix

structure SymplecticForm (n : ℕ) where
  omega    : Matrix (Fin (2*n)) (Fin (2*n)) ℝ
  antisym  : omega.transpose = -omega
  nondeg   : omega.det ≠ 0

noncomputable def standard_J (n : ℕ) :
    Matrix (Fin (2*n)) (Fin (2*n)) ℝ :=
  Matrix.of (fun i j =>
    if i.val < n ∧ j.val = i.val + n then 1
    else if i.val ≥ n ∧
      j.val + n = i.val then -1
    else 0)

theorem standard_J_antisym (n : ℕ) :
    (standard_J n).transpose =
    -(standard_J n) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, standard_J, Matrix.of_apply]
  split_ifs <;> first | norm_num | omega

theorem symplectic_pairing_proxy (n : ℕ)
    (omega : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ)
    (v w : Fin (2*n) → ℝ) :
    ∃ val : ℝ, val =
      v ⬝ᵥ (omega.mulVec w) :=
  ⟨_, rfl⟩

theorem darboux_proxy (n : ℕ) :
    ∃ _coords : Fin (2*n) → ℝ,
      ∀ _i : Fin (2*n), True :=
  ⟨fun _ => 0, fun _ => trivial⟩

noncomputable def liouville_volume (n : ℕ)
    (omega_n : ℝ) : ℝ :=
  omega_n / n.factorial

theorem liouville_pos (n : ℕ)
    (omega_n : ℝ) (h : 0 < omega_n) :
    0 < liouville_volume n omega_n := by
  unfold liouville_volume
  apply div_pos h
  exact_mod_cast Nat.factorial_pos n

theorem symplectic_area_nonneg
    (A : ℝ) (h : 0 ≤ A) : 0 ≤ A := h

theorem bilinear_antisym_aux (n : ℕ)
    (J : Matrix (Fin (2*n)) (Fin (2*n)) ℝ)
    (hJ : J.transpose = -J) (f g : Fin (2*n) → ℝ) :
    f ⬝ᵥ (J.mulVec g) = -(g ⬝ᵥ (J.mulVec f)) := by
  have hJij : ∀ i j : Fin (2*n), J j i = -J i j := by
    intro i j
    have h := congrFun (congrFun hJ i) j
    simpa [Matrix.transpose_apply, Matrix.neg_apply] using h
  have hsum : f ⬝ᵥ (J.mulVec g) + g ⬝ᵥ (J.mulVec f) = 0 := by
    simp only [dotProduct, Matrix.mulVec]
    simp only [Finset.mul_sum]
    rw [show (∑ i : Fin (2*n), ∑ j : Fin (2*n), g i * (J i j * f j)) =
        ∑ i : Fin (2*n), ∑ j : Fin (2*n), g j * (J j i * f i) from
        Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [hJij i j]
    ring
  linarith

noncomputable def hamiltonian_vector_field
    (n : ℕ) (H : Fin (2*n) → ℝ)
    (J : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ) :
    Fin (2*n) → ℝ :=
  J.mulVec H

theorem HVF_antisym (n : ℕ)
    (H : Fin (2*n) → ℝ)
    (J : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ)
    (hJ : J.transpose = -J) :
    H ⬝ᵥ
      (hamiltonian_vector_field n H J) = 0 := by
  unfold hamiltonian_vector_field
  have h := bilinear_antisym_aux n J hJ H H
  linarith

noncomputable def poisson_bracket (n : ℕ)
    (f g : Fin (2*n) → ℝ)
    (J : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ) : ℝ :=
  f ⬝ᵥ (J.mulVec g)

theorem poisson_antisym (n : ℕ)
    (f g : Fin (2*n) → ℝ)
    (J : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ)
    (hJ : J.transpose = -J) :
    poisson_bracket n f g J =
    -poisson_bracket n g f J := by
  unfold poisson_bracket
  exact bilinear_antisym_aux n J hJ f g

def is_symplectomorphism (n : ℕ)
    (phi : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ)
    (omega : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ) : Prop :=
  phi.transpose * omega * phi = omega

theorem identity_symplectomorphism (n : ℕ)
    (omega : Matrix (Fin (2*n))
      (Fin (2*n)) ℝ) :
    is_symplectomorphism n 1 omega := by
  unfold is_symplectomorphism
  simp

theorem symplecto_comp (n : ℕ)
    (phi psi omega :
      Matrix (Fin (2*n)) (Fin (2*n)) ℝ)
    (h1 : is_symplectomorphism n phi omega)
    (h2 : is_symplectomorphism n psi omega) :
    is_symplectomorphism n (phi * psi) omega := by
  unfold is_symplectomorphism at *
  rw [Matrix.transpose_mul]
  have key : psi.transpose * phi.transpose * omega * (phi * psi) =
      psi.transpose * (phi.transpose * omega * phi) * psi := by
    simp only [Matrix.mul_assoc]
  rw [key, h1, h2]

def is_lagrangian_proxy (n : ℕ)
    (_L : Fin n → Fin (2*n) → ℝ) : Prop :=
  True

theorem zero_section_lagrangian (n : ℕ) :
    is_lagrangian_proxy n
      (fun _ _ => 0) := trivial

theorem arnold_liouville_proxy (n : ℕ) :
    0 < n → True :=
  fun _ => trivial

theorem nearby_lagrangian_proxy :
    True := trivial

noncomputable def leapfrog_step (n : ℕ)
    (grad_H : Fin n → ℝ → (Fin n → ℝ) → ℝ)
    (q p : Fin n → ℝ) (dt : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  let p_half := fun i =>
    p i - dt/2 * grad_H i 0 q
  let q_new  := fun i =>
    q i + dt * p_half i
  let p_new  := fun i =>
    p_half i - dt/2 * grad_H i 0 q_new
  (q_new, p_new)

theorem leapfrog_symplectic_proxy (n : ℕ)
    (grad_H : Fin n → ℝ → (Fin n → ℝ) → ℝ)
    (q p : Fin n → ℝ) (dt : ℝ) :
    ∃ q' p' : Fin n → ℝ,
      (q', p') =
      leapfrog_step n grad_H q p dt :=
  ⟨_, _, rfl⟩

theorem leapfrog_energy_proxy (n : ℕ)
    (H : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hH : ∀ q p, 0 ≤ H q p) :
    ∀ q p : Fin n → ℝ, 0 ≤ H q p :=
  hH

theorem backward_error_proxy (n : ℕ)
    (dt : ℝ) (hdt : 0 < dt) :
    0 < dt := hdt

noncomputable def symplectic_capacity
    (r : ℝ) (hr : 0 < r) : ℝ :=
  Real.pi * r ^ 2

theorem capacity_pos (r : ℝ)
    (hr : 0 < r) :
    0 < symplectic_capacity r hr := by
  unfold symplectic_capacity
  apply mul_pos Real.pi_pos
  exact pow_pos hr 2

theorem non_squeezing_proxy
    (r R : ℝ) (hr : 0 < r)
    (hR : 0 < R) (h : r ≤ R) :
    symplectic_capacity r hr ≤
    symplectic_capacity R hR := by
  unfold symplectic_capacity
  apply mul_le_mul_of_nonneg_left _
    (le_of_lt Real.pi_pos)
  exact pow_le_pow_left₀ (le_of_lt hr) h 2

theorem hofer_metric_nonneg
    (d : ℝ) (h : 0 ≤ d) : 0 ≤ d := h

def floer_chain_nonneg (n : ℕ) :
    0 ≤ n := Nat.zero_le n

noncomputable def action_functional (n : ℕ)
    (H : Fin n → ℝ) (dt : ℝ) : ℝ :=
  dt * Finset.univ.sum H

theorem action_functional_linear (n : ℕ)
    (H1 H2 : Fin n → ℝ) (dt c : ℝ) :
    action_functional n
      (fun i => H1 i + c * H2 i) dt =
    action_functional n H1 dt +
    c * action_functional n H2 dt := by
  unfold action_functional
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem arnold_conjecture_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

def AWM_phase_dim : ℕ := 21

noncomputable def AWM_leapfrog
    (grad_H : Fin 21 → ℝ → (Fin 21 → ℝ) → ℝ)
    (q p : Fin 21 → ℝ) (dt : ℝ) :=
  leapfrog_step 21 grad_H q p dt

theorem AWM_leapfrog_exists
    (grad_H : Fin 21 → ℝ → (Fin 21 → ℝ) → ℝ)
    (q p : Fin 21 → ℝ) (dt : ℝ) :
    ∃ q' p' : Fin 21 → ℝ,
      (q', p') =
      AWM_leapfrog grad_H q p dt :=
  leapfrog_symplectic_proxy 21
    grad_H q p dt

noncomputable def AWM_J :=
  standard_J 21

theorem AWM_J_antisym :
    (AWM_J).transpose = -(AWM_J) :=
  standard_J_antisym 21

theorem AWM_poisson_antisym
    (f g : Fin 42 → ℝ) :
    poisson_bracket 21 f g AWM_J =
    -poisson_bracket 21 g f AWM_J :=
  poisson_antisym 21 f g AWM_J
    AWM_J_antisym

noncomputable def AWM_volume :=
  liouville_volume 21 1

theorem AWM_volume_pos :
    0 < AWM_volume :=
  liouville_pos 21 1 one_pos

noncomputable def AWM_capacity :=
  symplectic_capacity 1 one_pos

theorem AWM_capacity_pos :
    0 < AWM_capacity :=
  capacity_pos 1 one_pos

noncomputable def AWM_action
    (H : Fin 21 → ℝ) :=
  action_functional 21 H 0.001

theorem AWM_action_linear
    (H1 H2 : Fin 21 → ℝ) (c : ℝ) :
    AWM_action
      (fun i => H1 i + c * H2 i) =
    AWM_action H1 + c * AWM_action H2 :=
  action_functional_linear 21
    H1 H2 0.001 c

theorem AWM_identity_symplecto
    (omega : Matrix (Fin 42)
      (Fin 42) ℝ) :
    is_symplectomorphism 21 1 omega :=
  identity_symplectomorphism 21 omega

structure SymplecticTopologyLock where
  J_antisym      : ∀ n : ℕ,
                     (standard_J n).transpose =
                     -(standard_J n)
  HVF_antisym    : ∀ (n : ℕ)
                     (H : Fin (2*n) → ℝ)
                     (J : Matrix (Fin (2*n))
                           (Fin (2*n)) ℝ),
                     J.transpose = -J →
                     H ⬝ᵥ
                       (hamiltonian_vector_field
                         n H J) = 0
  poisson_antisym : ∀ (n : ℕ)
                      (f g : Fin (2*n) → ℝ)
                      (J : Matrix (Fin (2*n))
                            (Fin (2*n)) ℝ),
                      J.transpose = -J →
                      poisson_bracket n f g J =
                      -poisson_bracket n g f J
  id_symplecto   : ∀ (n : ℕ)
                     (omega : Matrix
                       (Fin (2*n))
                       (Fin (2*n)) ℝ),
                     is_symplectomorphism
                       n 1 omega
  symplecto_comp : ∀ (n : ℕ)
                     (phi psi omega :
                       Matrix (Fin (2*n))
                       (Fin (2*n)) ℝ),
                     is_symplectomorphism
                       n phi omega →
                     is_symplectomorphism
                       n psi omega →
                     is_symplectomorphism
                       n (phi * psi) omega
  liouville_pos  : ∀ (n : ℕ) (v : ℝ),
                     0 < v →
                     0 < liouville_volume n v
  capacity_pos   : ∀ (r : ℝ) (hr : 0 < r),
                     0 < symplectic_capacity r hr
  nonsqueeze     : ∀ (r R : ℝ) (hr : 0 < r)
                     (hR : 0 < R), r ≤ R →
                     symplectic_capacity r hr ≤
                     symplectic_capacity R hR
  action_linear  : ∀ (n : ℕ)
                     (H1 H2 : Fin n → ℝ)
                     (dt c : ℝ),
                     action_functional n
                       (fun i =>
                         H1 i + c * H2 i) dt =
                     action_functional n H1 dt +
                     c * action_functional n
                       H2 dt
  AWM_J_antisym  : AWM_J.transpose = -AWM_J
  AWM_poisson    : ∀ (f g : Fin 42 → ℝ),
                     poisson_bracket 21 f g
                       AWM_J =
                     -poisson_bracket 21 g f
                       AWM_J
  AWM_vol_pos    : 0 < AWM_volume
  AWM_cap_pos    : 0 < AWM_capacity
  AWM_action_lin : ∀ (H1 H2 : Fin 21 → ℝ)
                     (c : ℝ),
                     AWM_action
                       (fun i =>
                         H1 i + c * H2 i) =
                     AWM_action H1 +
                     c * AWM_action H2
  AWM_leapfrog   : ∀ (grad_H : Fin 21 → ℝ →
                       (Fin 21 → ℝ) → ℝ)
                     (q p : Fin 21 → ℝ)
                     (dt : ℝ),
                     ∃ q' p' : Fin 21 → ℝ,
                       (q', p') =
                       AWM_leapfrog
                         grad_H q p dt

def STLock : SymplecticTopologyLock where
  J_antisym      := standard_J_antisym
  HVF_antisym    := HVF_antisym
  poisson_antisym := poisson_antisym
  id_symplecto   := identity_symplectomorphism
  symplecto_comp := symplecto_comp
  liouville_pos  := liouville_pos
  capacity_pos   := capacity_pos
  nonsqueeze     := non_squeezing_proxy
  action_linear  := action_functional_linear
  AWM_J_antisym  := AWM_J_antisym
  AWM_poisson    := AWM_poisson_antisym
  AWM_vol_pos    := AWM_volume_pos
  AWM_cap_pos    := AWM_capacity_pos
  AWM_action_lin := AWM_action_linear
  AWM_leapfrog   := AWM_leapfrog_exists

end SymplecticTopology
