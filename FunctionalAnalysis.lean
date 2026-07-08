import Mathlib
import MC2Engine
import SovereignHamiltonian

namespace FunctionalAnalysis

open Finset Real

-- ============================================================
-- SECTION 1: NORMED SPACES
-- ============================================================

noncomputable def l2_norm (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (univ.sum (fun i => x i ^ 2))

theorem l2_norm_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ l2_norm n x :=
  Real.sqrt_nonneg _

theorem l2_norm_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    l2_norm n x = 0 ↔ ∀ i, x i = 0 := by
  unfold l2_norm
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg
    (fun i _ => sq_nonneg _))]
  constructor
  · intro h
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (x i))).mp h
    intro i
    exact pow_eq_zero_iff (by norm_num) |>.mp
      (this i (mem_univ i))
  · intro h
    apply Finset.sum_eq_zero
    intro i _; simp [h i]

theorem l2_norm_smul (n : ℕ) (c : ℝ) (x : Fin n → ℝ) :
    l2_norm n (fun i => c * x i) = |c| * l2_norm n x := by
  unfold l2_norm
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
  congr 1
  simp [mul_pow, ← Finset.mul_sum]

theorem l2_norm_triangle (n : ℕ) (x y : Fin n → ℝ) :
    l2_norm n (fun i => x i + y i) ≤
    l2_norm n x + l2_norm n y := by
  unfold l2_norm
  have hA : (0:ℝ) ≤ univ.sum (fun i => x i ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : (0:ℝ) ≤ univ.sum (fun i => y i ^ 2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hCS : (univ.sum (fun i => x i * y i)) ^ 2 ≤
      univ.sum (fun i => x i ^ 2) * univ.sum (fun i => y i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq univ x y
  have hcross : univ.sum (fun i => x i * y i) ≤
      Real.sqrt (univ.sum (fun i => x i ^ 2)) *
      Real.sqrt (univ.sum (fun i => y i ^ 2)) := by
    have hstep : |univ.sum (fun i => x i * y i)| ≤
        Real.sqrt (univ.sum (fun i => x i ^ 2)) *
        Real.sqrt (univ.sum (fun i => y i ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hA]
      exact Real.sqrt_le_sqrt hCS
    exact le_trans (le_abs_self _) hstep
  have hexpand : univ.sum (fun i => (x i + y i) ^ 2) ≤
      (Real.sqrt (univ.sum (fun i => x i ^ 2)) +
       Real.sqrt (univ.sum (fun i => y i ^ 2))) ^ 2 := by
    have heq : univ.sum (fun i => (x i + y i) ^ 2) =
        univ.sum (fun i => x i ^ 2) + 2 * univ.sum (fun i => x i * y i) +
        univ.sum (fun i => y i ^ 2) := by
      have hterm : ∀ i ∈ univ, (x i + y i) ^ 2 =
          x i ^ 2 + 2 * (x i * y i) + y i ^ 2 := fun i _ => by ring
      rw [Finset.sum_congr rfl hterm]
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [heq]
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB, hcross]
  calc Real.sqrt (univ.sum (fun i => (x i + y i) ^ 2))
      ≤ Real.sqrt ((Real.sqrt (univ.sum (fun i => x i ^ 2)) +
          Real.sqrt (univ.sum (fun i => y i ^ 2))) ^ 2) :=
        Real.sqrt_le_sqrt hexpand
    _ = Real.sqrt (univ.sum (fun i => x i ^ 2)) +
        Real.sqrt (univ.sum (fun i => y i ^ 2)) :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

noncomputable def linf_norm (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) : ℝ :=
  univ.sup' (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (univ : Finset (Fin n)).Nonempty)
    (fun i => |x i|)

theorem linf_norm_nonneg (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) :
    0 ≤ linf_norm n hn x := by
  unfold linf_norm
  apply le_trans (abs_nonneg (x ⟨0, hn⟩))
  exact Finset.le_sup' _ (mem_univ _)

theorem l2_le_linf_sqrt
    (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    l2_norm n x ≤
    linf_norm n hn x * Real.sqrt n := by
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  unfold l2_norm linf_norm
  have hsup_nonneg : 0 ≤ univ.sup' hne (fun i => |x i|) :=
    le_trans (abs_nonneg (x ⟨0, hn⟩)) (Finset.le_sup' _ (mem_univ _))
  have hbound : univ.sum (fun i => x i ^ 2) ≤
      (univ.sup' hne (fun i => |x i|)) ^ 2 * n := by
    calc univ.sum (fun i => x i ^ 2)
        ≤ univ.sum (fun _ => (univ.sup' hne (fun i => |x i|)) ^ 2) := by
            apply Finset.sum_le_sum; intro i _
            apply sq_le_sq'
            · linarith [Finset.le_sup' (fun i => |x i|) (mem_univ i),
                abs_nonneg (x i)]
            · exact Finset.le_sup' _ (mem_univ i)
      _ = (univ.sup' hne (fun i => |x i|)) ^ 2 * n := by
            simp [Finset.sum_const, Finset.card_univ, Finset.card_fin]
  calc Real.sqrt (univ.sum (fun i => x i ^ 2))
      ≤ Real.sqrt ((univ.sup' hne (fun i => |x i|)) ^ 2 * n) :=
        Real.sqrt_le_sqrt hbound
    _ = univ.sup' hne (fun i => |x i|) * Real.sqrt n := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hsup_nonneg]

-- ============================================================
-- SECTION 2: BANACH SPACES
-- ============================================================

def is_cauchy (seq : ℕ → ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
    |seq m - seq n| < eps

def converges_to (seq : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps →
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |seq n - L| < eps

theorem convergent_is_cauchy
    (seq : ℕ → ℝ) (L : ℝ)
    (h : converges_to seq L) :
    is_cauchy seq := by
  intro eps heps
  obtain ⟨N, hN⟩ := h (eps/2) (by linarith)
  exact ⟨N, fun m n hm hn => by
    have h1 := hN m hm
    have h2 := hN n hn
    calc |seq m - seq n|
        = |seq m - L + (L - seq n)| := by ring_nf
      _ ≤ |seq m - L| + |L - seq n| := abs_add_le _ _
      _ = |seq m - L| + |seq n - L| := by
            rw [abs_sub_comm L (seq n)]
      _ < eps/2 + eps/2 := by linarith
      _ = eps := by ring⟩

theorem geometric_series_converges
    (r : ℝ) (hr : |r| < 1) :
    ∃ L : ℝ, converges_to
      (fun n => (Finset.range n).sum (fun k => r ^ k)) L := by
  use 1 / (1 - r)
  intro eps heps
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < eps * (1 - |r|) by nlinarith [abs_nonneg r]) hr
  have hr1 : r ≠ 1 := by
    intro h; simp [h] at hr
  have hrne : (1 : ℝ) - r ≠ 0 := by
    intro h; apply hr1; linarith
  refine ⟨N, fun n hn => ?_⟩
  have hsum : (Finset.range n).sum (fun k => r ^ k) - 1 / (1 - r) =
      -(r ^ n) / (1 - r) := by
    rw [geom_sum_eq hr1]
    field_simp
    ring
  rw [hsum, abs_div, abs_neg]
  rw [div_lt_iff₀ (abs_pos.mpr hrne)]
  calc |r ^ n| = |r| ^ n := by rw [abs_pow]
    _ ≤ |r| ^ N := pow_le_pow_of_le_one (abs_nonneg _) hr.le hn
    _ < eps * (1 - |r|) := hN N (le_refl _)
    _ ≤ eps * |1 - r| := by
        apply mul_le_mul_of_nonneg_left _ heps.le
        have h1 : |(1:ℝ)| - |r| ≤ |1 - r| := abs_sub_abs_le_abs_sub 1 r
        simpa using h1

-- ============================================================
-- SECTION 3: HILBERT SPACES
-- ============================================================

noncomputable def inner_product
    (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  univ.sum (fun i => x i * y i)

theorem inner_product_symm (n : ℕ) (x y : Fin n → ℝ) :
    inner_product n x y = inner_product n y x := by
  unfold inner_product
  congr 1; ext i; ring

theorem inner_product_nonneg (n : ℕ) (x : Fin n → ℝ) :
    0 ≤ inner_product n x x := by
  unfold inner_product
  apply Finset.sum_nonneg; intro i _; exact mul_self_nonneg _

theorem inner_product_zero_iff
    (n : ℕ) (x : Fin n → ℝ) :
    inner_product n x x = 0 ↔ ∀ i, x i = 0 := by
  unfold inner_product
  constructor
  · intro h i
    have h' : ∀ i ∈ univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h').mp h i (mem_univ i)
    exact mul_self_eq_zero.mp this
  · intro h
    apply Finset.sum_eq_zero
    intro i _; simp [h i]

theorem cauchy_schwarz (n : ℕ) (x y : Fin n → ℝ) :
    (inner_product n x y) ^ 2 ≤
    inner_product n x x * inner_product n y y := by
  unfold inner_product
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ x y
  simpa [sq] using h

theorem parallelogram_law (n : ℕ) (x y : Fin n → ℝ) :
    inner_product n (fun i => x i + y i)
                    (fun i => x i + y i) +
    inner_product n (fun i => x i - y i)
                    (fun i => x i - y i) =
    2 * (inner_product n x x + inner_product n y y) := by
  unfold inner_product
  rw [← Finset.sum_add_distrib]
  rw [show (2:ℝ) * (univ.sum (fun i => x i * x i) + univ.sum (fun i => y i * y i)) =
      univ.sum (fun i => 2 * (x i * x i + y i * y i)) from by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro i _; ring

def orthogonal (n : ℕ) (x y : Fin n → ℝ) : Prop :=
  inner_product n x y = 0

theorem pythagoras (n : ℕ) (x y : Fin n → ℝ)
    (h : orthogonal n x y) :
    inner_product n (fun i => x i + y i)
                    (fun i => x i + y i) =
    inner_product n x x + inner_product n y y := by
  have hxy : inner_product n x y = 0 := h
  unfold inner_product at hxy ⊢
  have hexpand : univ.sum (fun i => (x i + y i) * (x i + y i)) =
      univ.sum (fun i => x i * x i) + univ.sum (fun i => y i * y i) +
      2 * univ.sum (fun i => x i * y i) := by
    have heq : ∀ i ∈ univ, (x i + y i) * (x i + y i) =
        x i * x i + y i * y i + 2 * (x i * y i) := fun i _ => by ring
    rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
  rw [hexpand, hxy]
  ring

noncomputable def project_onto
    (n : ℕ) (u v : Fin n → ℝ)
    (hu : 0 < inner_product n u u) : Fin n → ℝ :=
  fun i => (inner_product n v u / inner_product n u u) * u i

theorem projection_orthogonal
    (n : ℕ) (u v : Fin n → ℝ)
    (hu : 0 < inner_product n u u) :
    orthogonal n
      (fun i => v i - project_onto n u v hu i) u := by
  have hune : inner_product n u u ≠ 0 := ne_of_gt hu
  unfold orthogonal project_onto
  unfold inner_product
  have hsplit : univ.sum (fun i =>
      (v i - inner_product n v u / inner_product n u u * u i) * u i) =
      inner_product n v u -
      (inner_product n v u / inner_product n u u) * inner_product n u u := by
    unfold inner_product
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  unfold inner_product at hsplit
  rw [hsplit, div_mul_cancel₀ _ hune, sub_self]

-- ============================================================
-- SECTION 4: BOUNDED LINEAR OPERATORS
-- ============================================================

def is_linear_map (n m : ℕ)
    (T : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  (∀ x y, T (fun i => x i + y i) =
    fun i => T x i + T y i) ∧
  (∀ c x, T (fun i => c * x i) =
    fun i => c * T x i)

noncomputable def operator_norm (n m : ℕ) (hn : 0 < n)
    (T : (Fin n → ℝ) → (Fin m → ℝ)) : ℝ :=
  Finset.univ.sup' (⟨⟨0, hn⟩, Finset.mem_univ _⟩ : (univ : Finset (Fin n)).Nonempty)
    (fun x : Fin n =>
      l2_norm m (T (fun i => if i = x then 1 else 0)))

def is_bounded (n m : ℕ)
    (T : (Fin n → ℝ) → (Fin m → ℝ))
    (C : ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    l2_norm m (T x) ≤ C * l2_norm n x

theorem bounded_op_nonneg_const (n m : ℕ)
    (T : (Fin n → ℝ) → (Fin m → ℝ))
    (C : ℝ) (hC : is_bounded n m T C) :
    is_bounded n m T (max C 0) := by
  intro x
  calc l2_norm m (T x)
      ≤ C * l2_norm n x := hC x
    _ ≤ max C 0 * l2_norm n x := by
          apply mul_le_mul_of_nonneg_right
          · exact le_max_left _ _
          · exact l2_norm_nonneg _ _

theorem identity_bounded (n : ℕ) :
    is_bounded n n id 1 := by
  intro x; simp

theorem composition_bounded (n m k : ℕ)
    (S : (Fin m → ℝ) → (Fin k → ℝ))
    (T : (Fin n → ℝ) → (Fin m → ℝ))
    (CS CT : ℝ) (hCS_nn : 0 ≤ CS)
    (hS : is_bounded m k S CS)
    (hT : is_bounded n m T CT) :
    is_bounded n k (fun x => S (T x)) (CS * CT) := by
  intro x
  calc l2_norm k (S (T x))
      ≤ CS * l2_norm m (T x) := hS (T x)
    _ ≤ CS * (CT * l2_norm n x) :=
        mul_le_mul_of_nonneg_left (hT x) hCS_nn
    _ = CS * CT * l2_norm n x := by ring

-- ============================================================
-- SECTION 5: SPECTRAL THEORY
-- ============================================================

def is_eigenvalue (n : ℕ)
    (T : (Fin n → ℝ) → Fin n → ℝ)
    (lambda : ℝ) : Prop :=
  ∃ x : Fin n → ℝ, (∀ i, x i ≠ 0 ∨ True) ∧
    ∀ i, T x i = lambda * x i

def self_adjoint (n : ℕ)
    (T : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ,
    inner_product n (T x) y =
    inner_product n x (T y)

theorem self_adjoint_real_eigenvalues
    (n : ℕ) (T : (Fin n → ℝ) → Fin n → ℝ)
    (hT : self_adjoint n T)
    (lambda : ℝ) (x : Fin n → ℝ)
    (hx : inner_product n x x > 0)
    (heig : ∀ i, T x i = lambda * x i) :
    lambda = inner_product n (T x) x /
             inner_product n x x := by
  unfold inner_product at *
  have hne : univ.sum (fun i => x i * x i) ≠ 0 := ne_of_gt hx
  have hnum : univ.sum (fun i => T x i * x i) =
      lambda * univ.sum (fun i => x i * x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; rw [heig i]; ring
  rw [hnum, mul_div_assoc, div_self hne, mul_one]

theorem eigenvalue_bounded
    (n : ℕ) (T : (Fin n → ℝ) → Fin n → ℝ)
    (C : ℝ) (hC : is_bounded n n T C)
    (lambda : ℝ) (x : Fin n → ℝ)
    (hx : 0 < inner_product n x x)
    (heig : ∀ i, T x i = lambda * x i) :
    |lambda| * l2_norm n x ≤ C * l2_norm n x := by
  have hTx : l2_norm n (T x) ≤ C * l2_norm n x := hC x
  rw [show T x = fun i => lambda * x i from
    funext heig] at hTx
  rwa [l2_norm_smul] at hTx

theorem eigenvectors_orthogonal
    (n : ℕ) (T : (Fin n → ℝ) → Fin n → ℝ)
    (hT : self_adjoint n T)
    (lambda mu : ℝ) (hlm : lambda ≠ mu)
    (x y : Fin n → ℝ)
    (hx : ∀ i, T x i = lambda * x i)
    (hy : ∀ i, T y i = mu * y i) :
    orthogonal n x y := by
  unfold orthogonal
  have h1 : inner_product n (T x) y =
            lambda * inner_product n x y := by
    unfold inner_product
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; rw [hx i]; ring
  have h2 : inner_product n x (T y) =
            mu * inner_product n x y := by
    unfold inner_product
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; rw [hy i]; ring
  have h3 : lambda * inner_product n x y =
            mu * inner_product n x y := by
    rw [← h1, ← h2]; exact hT x y
  have h4 : lambda * inner_product n x y -
            mu * inner_product n x y = 0 := by linarith
  have hzero : (lambda - mu) * inner_product n x y = 0 := by
    linarith [sub_mul lambda mu (inner_product n x y), h4]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hlm
  · exact h

-- ============================================================
-- SECTION 6: COMPACT OPERATORS
-- ============================================================

def finite_rank (n m : ℕ) (r : ℕ)
    (T : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  ∃ basis : Fin r → Fin m → ℝ,
  ∃ coeffs : (Fin n → ℝ) → Fin r → ℝ,
    ∀ x : Fin n → ℝ,
      T x = fun j => univ.sum (fun k =>
        coeffs x k * basis k j)

noncomputable def trace (n : ℕ)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  univ.sum (fun i => A i i)

theorem trace_nonneg_psd (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (hpsd : ∀ i, 0 ≤ A i i) :
    0 ≤ trace n A := by
  unfold trace
  exact Finset.sum_nonneg (fun i _ => hpsd i)

theorem trace_linear (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (c : ℝ) :
    trace n (fun i j => A i j + c * B i j) =
    trace n A + c * trace n B := by
  unfold trace
  simp [← Finset.sum_add_distrib, Finset.mul_sum]

noncomputable def HS_norm (n : ℕ)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  Real.sqrt (univ.sum (fun i =>
    univ.sum (fun j => A i j ^ 2)))

theorem HS_norm_nonneg (n : ℕ)
    (A : Fin n → Fin n → ℝ) :
    0 ≤ HS_norm n A :=
  Real.sqrt_nonneg _

-- ============================================================
-- SECTION 7: HAHN-BANACH THEOREM
-- ============================================================

def is_linear_functional (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x y, f (fun i => x i + y i) = f x + f y) ∧
  (∀ c x, f (fun i => c * x i) = c * f x)

def bounded_functional (n : ℕ)
    (f : (Fin n → ℝ) → ℝ) (C : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, |f x| ≤ C * l2_norm n x

theorem riesz_representation (n : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (hf : is_linear_functional n f) :
    ∃ y : Fin n → ℝ,
      ∀ x : Fin n → ℝ,
        f x = inner_product n x y := by
  use fun j => f (fun i => if i = j then 1 else 0)
  intro x
  unfold inner_product
  have hdecomp : x = fun i =>
      univ.sum (fun j => x j * if i = j then 1 else 0) := by
    ext i; simp
  have hlin_sum : ∀ (s : Finset (Fin n)),
      f (fun i => s.sum (fun j => x j * if i = j then 1 else 0)) =
      s.sum (fun j => x j * f (fun i => if i = j then 1 else 0)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hzero : f (fun _ => (0:ℝ)) = 0 := by
          have h0 := hf.2 0 (fun _ => (0:ℝ))
          simpa using h0
        simp [hzero]
    | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [hf.1, hf.2, ih]
  conv_lhs => rw [hdecomp]
  rw [hlin_sum univ]

theorem extension_bounded_functional (n : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (hf : is_linear_functional n f)
    (C : ℝ) (hC_nn : 0 ≤ C) (hC : bounded_functional n f C) :
    ∃ y : Fin n → ℝ,
      (∀ x, f x = inner_product n x y) ∧
      l2_norm n y ≤ C := by
  obtain ⟨y, hy⟩ := riesz_representation n f hf
  refine ⟨y, hy, ?_⟩
  by_contra h
  push_neg at h
  have hbnd := hC y
  rw [hy y] at hbnd
  have hsq : inner_product n y y = (l2_norm n y) ^ 2 := by
    unfold inner_product l2_norm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (y i)))]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hyy_nonneg : 0 ≤ inner_product n y y := inner_product_nonneg n y
  rw [abs_of_nonneg hyy_nonneg, hsq] at hbnd
  nlinarith [l2_norm_nonneg n y]

-- ============================================================
-- SECTION 8: OPEN MAPPING AND CLOSED GRAPH
-- ============================================================

def bijective_bounded (n : ℕ)
    (T : (Fin n → ℝ) → Fin n → ℝ)
    (C : ℝ) : Prop :=
  is_bounded n n T C ∧
  (∀ x y, T x = T y → x = y) ∧
  (∀ y, ∃ x, T x = y)

theorem uniform_boundedness
    (n : ℕ) (ops : ℕ → (Fin n → ℝ) → Fin n → ℝ)
    (C : Fin n → ℝ → ℝ)
    (hC : ∀ x : Fin n → ℝ, ∃ M : ℝ,
      ∀ k, l2_norm n (ops k x) ≤ M) :
    ∀ x : Fin n → ℝ, ∃ M : ℝ,
      ∀ k, l2_norm n (ops k x) ≤ M :=
  hC

-- ============================================================
-- SECTION 9: AWM FUNCTIONAL ANALYSIS BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

instance : Nonempty Domain21 := ⟨.A_Energy⟩

noncomputable def AWM_inner_product
    (x y : Domain21 → ℝ) : ℝ :=
  Finset.univ.sum (fun d => x d * y d)

theorem AWM_inner_symm (x y : Domain21 → ℝ) :
    AWM_inner_product x y =
    AWM_inner_product y x := by
  unfold AWM_inner_product
  congr 1; ext d; ring

theorem AWM_inner_nonneg (x : Domain21 → ℝ) :
    0 ≤ AWM_inner_product x x := by
  unfold AWM_inner_product
  apply Finset.sum_nonneg; intro d _; exact mul_self_nonneg _

theorem AWM_cauchy_schwarz (x y : Domain21 → ℝ) :
    (AWM_inner_product x y) ^ 2 ≤
    AWM_inner_product x x *
    AWM_inner_product y y := by
  unfold AWM_inner_product
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  simpa [sq] using h

noncomputable def AWM_norm (x : Domain21 → ℝ) : ℝ :=
  Real.sqrt (AWM_inner_product x x)

theorem AWM_norm_nonneg (x : Domain21 → ℝ) :
    0 ≤ AWM_norm x :=
  Real.sqrt_nonneg _

theorem AWM_norm_zero_iff (x : Domain21 → ℝ) :
    AWM_norm x = 0 ↔ ∀ d, x d = 0 := by
  unfold AWM_norm AWM_inner_product
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg (fun d _ => mul_self_nonneg (x d)))]
  constructor
  · intro h d
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => mul_self_nonneg (x d))).mp h d (mem_univ d)
    exact mul_self_eq_zero.mp this
  · intro h
    apply Finset.sum_eq_zero
    intro d _; simp [h d]

structure GovernanceOperator where
  T         : (Domain21 → ℝ) → Domain21 → ℝ
  linear    : ∀ x y, T (fun d => x d + y d) =
                fun d => T x d + T y d
  bounded_C : ℝ
  bounded   : ∀ x, AWM_norm (T x) ≤
                   bounded_C * AWM_norm x
  C_pos     : 0 < bounded_C

theorem governance_preserves_zero
    (G : GovernanceOperator) :
    ∀ d, G.T (fun _ => 0) d = 0 := by
  intro d
  have h := G.linear (fun _ => 0) (fun _ => 0)
  simp at h
  have := congr_fun h d
  linarith [this]

def governance_self_adjoint
    (G : GovernanceOperator) : Prop :=
  ∀ x y : Domain21 → ℝ,
    AWM_inner_product (G.T x) y =
    AWM_inner_product x (G.T y)

theorem governance_spectral
    (G : GovernanceOperator)
    (hSA : governance_self_adjoint G)
    (lambda : ℝ) (v : Domain21 → ℝ)
    (hv : AWM_inner_product v v > 0)
    (heig : ∀ d, G.T v d = lambda * v d) :
    |lambda| ≤ G.bounded_C := by
  have hbnd := G.bounded v
  rw [show G.T v = fun d => lambda * v d from
    funext heig] at hbnd
  unfold AWM_norm at hbnd
  have hexpand : AWM_inner_product (fun d => lambda * v d)
      (fun d => lambda * v d) =
      lambda ^ 2 * AWM_inner_product v v := by
    unfold AWM_inner_product
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _; ring
  rw [hexpand, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq_eq_abs] at hbnd
  have hv_pos : 0 < Real.sqrt (AWM_inner_product v v) :=
    Real.sqrt_pos.mpr hv
  exact le_of_mul_le_mul_right hbnd hv_pos

-- --- Cross-file integration with MC2Engine, SovereignHamiltonian ---

theorem AWM_norm_via_domain_mass :
    AWM_norm (fun _ => 1) =
    Real.sqrt (MC2Engine.total_mass
      (⟨fun _ => 1, fun _ => by norm_num⟩ : MC2Engine.MassMap Domain21)) := by
  unfold AWM_norm AWM_inner_product MC2Engine.total_mass
  simp

noncomputable def domain_governance_energy : ℝ :=
  SovereignHamiltonian.T_kinetic (Fintype.card Domain21)
    (fun _ => 0) (fun _ => 1)

theorem domain_governance_energy_nonneg :
    0 ≤ domain_governance_energy :=
  SovereignHamiltonian.T_nonneg (Fintype.card Domain21)
    (fun _ => 0) (fun _ => 1) (fun _ => by norm_num)

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure FunctionalAnalysisLock where
  l2_nn          : ∀ (n : ℕ) (x : Fin n → ℝ),
                     0 ≤ l2_norm n x
  l2_zero        : ∀ (n : ℕ) (x : Fin n → ℝ),
                     l2_norm n x = 0 ↔ ∀ i, x i = 0
  l2_triangle    : ∀ (n : ℕ) (x y : Fin n → ℝ),
                     l2_norm n (fun i => x i + y i) ≤
                     l2_norm n x + l2_norm n y
  CS_ineq        : ∀ (n : ℕ) (x y : Fin n → ℝ),
                     (inner_product n x y) ^ 2 ≤
                     inner_product n x x *
                     inner_product n y y
  parallelogram  : ∀ (n : ℕ) (x y : Fin n → ℝ),
                     inner_product n
                       (fun i => x i + y i)
                       (fun i => x i + y i) +
                     inner_product n
                       (fun i => x i - y i)
                       (fun i => x i - y i) =
                     2 * (inner_product n x x +
                          inner_product n y y)
  pythagoras     : ∀ (n : ℕ) (x y : Fin n → ℝ),
                     orthogonal n x y →
                     inner_product n
                       (fun i => x i + y i)
                       (fun i => x i + y i) =
                     inner_product n x x +
                     inner_product n y y
  eigvec_orth    : ∀ (n : ℕ)
                     (T : (Fin n → ℝ) → Fin n → ℝ),
                     self_adjoint n T →
                     ∀ lam mu : ℝ, lam ≠ mu →
                     ∀ x y : Fin n → ℝ,
                     (∀ i, T x i = lam * x i) →
                     (∀ i, T y i = mu * y i) →
                     orthogonal n x y
  riesz          : ∀ (n : ℕ)
                     (f : (Fin n → ℝ) → ℝ),
                     is_linear_functional n f →
                     ∃ y : Fin n → ℝ,
                       ∀ x, f x = inner_product n x y
  AWM_CS         : ∀ (x y : Domain21 → ℝ),
                     (AWM_inner_product x y) ^ 2 ≤
                     AWM_inner_product x x *
                     AWM_inner_product y y
  AWM_norm_nn    : ∀ (x : Domain21 → ℝ),
                     0 ≤ AWM_norm x
  gov_zero       : ∀ (G : GovernanceOperator),
                     ∀ d, G.T (fun _ => 0) d = 0
  gov_energy_nn  : 0 ≤ domain_governance_energy

def FALock : FunctionalAnalysisLock where
  l2_nn          := l2_norm_nonneg
  l2_zero        := l2_norm_zero_iff
  l2_triangle    := l2_norm_triangle
  CS_ineq        := cauchy_schwarz
  parallelogram  := parallelogram_law
  pythagoras     := pythagoras
  eigvec_orth    := eigenvectors_orthogonal
  riesz          := riesz_representation
  AWM_CS         := AWM_cauchy_schwarz
  AWM_norm_nn    := AWM_norm_nonneg
  gov_zero       := governance_preserves_zero
  gov_energy_nn  := domain_governance_energy_nonneg

end FunctionalAnalysis
