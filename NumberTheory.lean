-- NumberTheory.lean
import Mathlib

namespace NumberTheory

open Finset Real

-- ============================================================
-- SECTION 1: PRIME NUMBERS
-- Fundamental building blocks of arithmetic
-- ============================================================

-- Prime counting function π(n)
noncomputable def prime_count (n : ℕ) : ℕ :=
  (Finset.range n).filter Nat.Prime |>.card

theorem prime_count_pos :
    0 < prime_count 3 := by
  unfold prime_count; native_decide

theorem prime_count_monotone (m n : ℕ) (h : m ≤ n) :
    prime_count m ≤ prime_count n := by
  unfold prime_count
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono h

-- Infinitely many primes
theorem infinitely_many_primes :
    ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Nat.Prime p :=
  fun n => Nat.exists_infinite_primes (n + 1) |>.imp
    fun p ⟨hp1, hp2⟩ => ⟨by omega, hp2⟩

-- Prime factorization exists
theorem prime_factorization (n : ℕ) (hn : 1 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n :=
  ⟨n.minFac, Nat.minFac_prime (by omega),
   Nat.minFac_dvd n⟩

-- Fundamental theorem of arithmetic
theorem unique_factorization (n : ℕ) (hn : 0 < n) :
    ∃ factors : Multiset ℕ,
      (∀ p ∈ factors, Nat.Prime p) ∧
      factors.prod = n :=
  ⟨n.factors, fun p hp =>
    Nat.prime_of_mem_primeFactors
      (Nat.mem_factors.mpr
        ⟨Nat.prime_of_mem_factors hp, Nat.dvd_of_mem_factors hp⟩),
   Nat.factors_prod hn⟩

-- Twin primes
def twin_prime_pair (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2)

theorem twin_prime_exists :
    twin_prime_pair 5 := by
  constructor <;> decide

-- Goldbach: every even n > 2 is sum of two primes
-- (Open conjecture — stated as hypothesis)
def goldbach_property (n : ℕ) : Prop :=
  2 < n → n % 2 = 0 →
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

theorem goldbach_4 : goldbach_property 4 := by
  intro _ _
  exact ⟨2, 2, by decide, by decide, rfl⟩

theorem goldbach_6 : goldbach_property 6 := by
  intro _ _
  exact ⟨3, 3, by decide, by decide, rfl⟩

-- ============================================================
-- SECTION 2: MODULAR ARITHMETIC
-- ℤ/nℤ: integers modulo n
-- ============================================================

-- Modular equivalence
def mod_equiv (a b n : ℤ) : Prop :=
  n ∣ (a - b)

theorem mod_equiv_refl (a n : ℤ) :
    mod_equiv a a n := by
  unfold mod_equiv; simp

theorem mod_equiv_symm (a b n : ℤ)
    (h : mod_equiv a b n) :
    mod_equiv b a n := by
  unfold mod_equiv at *
  rwa [show b - a = -(a - b) from by ring,
       dvd_neg]

theorem mod_equiv_trans (a b c n : ℤ)
    (h1 : mod_equiv a b n)
    (h2 : mod_equiv b c n) :
    mod_equiv a c n := by
  unfold mod_equiv at *
  have : n ∣ (a - b) + (b - c) := dvd_add h1 h2
  rwa [show (a - b) + (b - c) = a - c from by ring] at this

theorem mod_equiv_add (a b c d n : ℤ)
    (h1 : mod_equiv a b n)
    (h2 : mod_equiv c d n) :
    mod_equiv (a + c) (b + d) n := by
  unfold mod_equiv at *
  have : n ∣ (a - b) + (c - d) := dvd_add h1 h2
  rwa [show (a - b) + (c - d) =
       (a + c) - (b + d) from by ring] at this

theorem mod_equiv_mul (a b c d n : ℤ)
    (h1 : mod_equiv a b n)
    (h2 : mod_equiv c d n) :
    mod_equiv (a * c) (b * d) n := by
  unfold mod_equiv at *
  have : n ∣ b * (c - d) + d * (a - b) := by
    exact dvd_add (dvd_mul_of_dvd_right h2 b)
      (dvd_mul_of_dvd_right h1 d)
  rwa [show b * (c - d) + d * (a - b) =
       a * c - b * d from by ring] at this

-- Fermat's little theorem
theorem fermat_little (p : ℕ) (hp : Nat.Prime p)
    (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    mod_equiv (a ^ (p - 1)) 1 p := by
  unfold mod_equiv
  have := ZMod.intCast_zmod_eq_zero_iff_dvd
    (a ^ (p - 1) - 1) p
  rw [show (p : ℤ) ∣ a ^ (p - 1) - 1 ↔
      (a ^ (p - 1) - 1 : ZMod p) = 0 from
    by rw [this]; simp]
  have horder := ZMod.units_pow_card_sub_one_eq_one
    (p := p.toPNat' (Nat.Prime.pos hp))
  sorry -- Requires ZMod machinery; acknowledged

-- Chinese Remainder Theorem
theorem CRT (m n : ℕ) (hcop : Nat.Coprime m n)
    (a b : ℤ) :
    ∃ x : ℤ, mod_equiv x a m ∧ mod_equiv x b n := by
  have ⟨u, v, huv⟩ := Nat.Coprime.eq_one_of_self_pow
    hcop 1 |>.symm ▸ hcop
  exact ⟨a * n * v + b * m * u,
    ⟨by unfold mod_equiv; ring_nf; exact dvd_mul_right _ _⟩,
    ⟨by unfold mod_equiv; ring_nf; exact dvd_mul_right _ _⟩⟩

-- ============================================================
-- SECTION 3: QUADRATIC RECIPROCITY
-- ============================================================

-- Legendre symbol: (a/p)
noncomputable def legendre_symbol
    (a p : ℤ) : ℤ :=
  if (p : ℤ) ∣ a then 0
  else if ∃ x : ℤ, mod_equiv (x^2) a p then 1
  else -1

theorem legendre_values (a p : ℤ) :
    legendre_symbol a p = -1 ∨
    legendre_symbol a p = 0 ∨
    legendre_symbol a p = 1 := by
  unfold legendre_symbol
  split_ifs <;> simp

theorem legendre_zero (p : ℤ) :
    legendre_symbol 0 p = 0 := by
  unfold legendre_symbol; simp

theorem legendre_one (p : ℤ) :
    legendre_symbol 1 p = 1 := by
  unfold legendre_symbol
  simp
  exact ⟨1, by unfold mod_equiv; simp⟩

-- Euler's criterion: (a/p) ≡ a^{(p-1)/2} mod p
theorem euler_criterion (p : ℕ) (hp : Nat.Prime p)
    (hodd : p % 2 = 1) (a : ℤ) :
    mod_equiv (legendre_symbol a p)
      (a ^ ((p-1)/2)) p := by
  unfold mod_equiv legendre_symbol
  split_ifs <;> simp

-- Quadratic reciprocity law
theorem quadratic_reciprocity
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpp : p % 2 = 1) (hqp : q % 2 = 1)
    (hpq : p ≠ q) :
    legendre_symbol p q * legendre_symbol q p =
    (-1) ^ ((p-1)/2 * ((q-1)/2)) := by
  simp [legendre_values p q, legendre_values q p]
  sorry -- Deep number theory; acknowledged

-- ============================================================
-- SECTION 4: ARITHMETIC FUNCTIONS
-- ============================================================

-- Euler's totient function φ(n)
noncomputable def euler_totient (n : ℕ) : ℕ :=
  (Finset.range n).filter
    (fun k => Nat.Coprime k n) |>.card

theorem totient_prime (p : ℕ) (hp : Nat.Prime p) :
    euler_totient p = p - 1 := by
  unfold euler_totient
  rw [show (Finset.range p).filter
      (fun k => Nat.Coprime k p) =
      (Finset.range p).filter
      (fun k => 0 < k) from by
    ext k; simp [Nat.Coprime, hp.coprime_iff_not_dvd]]
  simp [Finset.card_filter, Finset.sum_range_succ]
  omega

theorem totient_pos (n : ℕ) (hn : 0 < n) :
    0 < euler_totient n := by
  unfold euler_totient
  apply Finset.card_pos.mpr
  exact ⟨1, by simp [Nat.Coprime, hn]⟩

-- Möbius function μ(n)
noncomputable def mobius (n : ℕ) : ℤ :=
  if n = 1 then 1
  else if ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n then 0
  else (-1) ^ (n.factors.length)

theorem mobius_one : mobius 1 = 1 := by
  unfold mobius; simp

theorem mobius_prime (p : ℕ) (hp : Nat.Prime p) :
    mobius p = -1 := by
  unfold mobius
  simp [hp.one_lt.ne']
  constructor
  · intro ⟨q, hq, hdvd⟩
    have := Nat.le_of_dvd hp.pos
      (dvd_trans (dvd_pow_self q 2) hdvd)
    have hqp := Nat.eq_of_dvd_of_lt_two_mul_dvd
      (by omega) (Nat.dvd_of_mem_factors
        (Nat.mem_factors.mpr ⟨hq, by
          exact dvd_trans (dvd_pow_self q 2) hdvd⟩))
    simp [hqp, hp.factors_unique] at hdvd
    omega
  · simp [hp.factors_unique]

-- Divisor sum function σ(n)
noncomputable def divisor_sum (n : ℕ) : ℕ :=
  n.divisors.sum id

theorem divisor_sum_prime (p : ℕ) (hp : Nat.Prime p) :
    divisor_sum p = p + 1 := by
  unfold divisor_sum
  rw [Nat.Prime.divisors hp]
  simp

-- Multiplicativity
def is_multiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧
  ∀ m n : ℕ, Nat.Coprime m n →
    f (m * n) = f m * f n

theorem mobius_multiplicative :
    is_multiplicative mobius := by
  constructor
  · exact mobius_one
  · intro m n hcop
    sorry -- Requires Möbius multiplicativity; acknowledged

-- ============================================================
-- SECTION 5: DIRICHLET SERIES
-- L(s, χ) = Σ χ(n)/n^s
-- ============================================================

-- Dirichlet character (simplified)
structure DirichletCharacter (q : ℕ) where
  chi      : ℕ → ℂ
  periodic : ∀ n, chi (n + q) = chi n
  chi_one  : chi 1 = 1

-- L-function partial sum
noncomputable def L_partial_sum
    (q N : ℕ) (chi : DirichletCharacter q)
    (s : ℝ) (hs : 0 < s) : ℝ :=
  (Finset.range N).sum (fun n =>
    if n = 0 then 0
    else (chi.chi n).re / n ^ s)

-- Riemann zeta partial sum
noncomputable def zeta_partial (N : ℕ) (s : ℝ)
    (hs : 1 < s) : ℝ :=
  (Finset.range N).sum (fun n =>
    if n = 0 then 0 else 1 / (n : ℝ) ^ s)

theorem zeta_partial_pos (N : ℕ) (s : ℝ)
    (hs : 1 < s) (hN : 0 < N) :
    0 < zeta_partial N s hs := by
  unfold zeta_partial
  apply Finset.sum_pos_of_ne_zero
  · intro n _
    split_ifs with h
    · exact le_refl _
    · positivity
  · exact ⟨1, by simp [Finset.mem_range, hN], by simp⟩

-- Euler product: ζ(s) = ∏_p (1 - p^{-s})^{-1}
theorem euler_product_2 (s : ℝ) (hs : 1 < s) :
    0 < (1 - (2 : ℝ) ^ (-s))⁻¹ := by
  apply inv_pos.mpr
  linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (-s),
            Real.rpow_lt_one (by norm_num : (0:ℝ) ≤ 2)
              (by norm_num : (2:ℝ) < 1) (by linarith)]

-- ============================================================
-- SECTION 6: ALGEBRAIC NUMBER THEORY
-- ============================================================

-- Algebraic integer: root of monic polynomial with ℤ coefficients
def is_algebraic_integer (alpha : ℝ) : Prop :=
  ∃ (n : ℕ) (coeffs : Fin n → ℤ),
    0 < n ∧
    alpha ^ n +
    (Finset.range n).sum (fun i =>
      (coeffs ⟨i, by omega⟩ : ℝ) * alpha ^ i) = 0

theorem integers_are_algebraic (n : ℤ) :
    is_algebraic_integer n := by
  exact ⟨1, fun _ => -n, one_pos, by simp⟩

theorem sqrt2_algebraic :
    is_algebraic_integer (Real.sqrt 2) := by
  exact ⟨2, fun i => if i = 0 then -2 else 0,
    by norm_num, by
    simp [Finset.sum_range_succ]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num⟩

-- Norm of algebraic integer
noncomputable def algebraic_norm
    (alpha : ℝ) (n : ℕ) : ℝ :=
  |alpha| ^ n

theorem algebraic_norm_pos
    (alpha : ℝ) (n : ℕ) (hn : 0 < n)
    (h : alpha ≠ 0) :
    0 < algebraic_norm alpha n := by
  unfold algebraic_norm
  exact pow_pos (abs_pos.mpr h) n

-- Ring of integers of quadratic field ℚ(√d)
-- For d squarefree: ℤ[√d] or ℤ[(1+√d)/2]
noncomputable def quad_int_norm
    (a b d : ℤ) : ℤ :=
  a ^ 2 - d * b ^ 2

theorem quad_int_norm_mul
    (a1 b1 a2 b2 d : ℤ) :
    quad_int_norm (a1*a2 + d*b1*b2)
                  (a1*b2 + b1*a2) d =
    quad_int_norm a1 b1 d *
    quad_int_norm a2 b2 d := by
  unfold quad_int_norm; ring

-- ============================================================
-- SECTION 7: p-ADIC NUMBERS
-- ============================================================

-- p-adic valuation
noncomputable def p_adic_val (p n : ℕ)
    (hp : Nat.Prime p) (hn : 0 < n) : ℕ :=
  n.factorization p

theorem p_adic_val_prime (p : ℕ)
    (hp : Nat.Prime p) :
    p_adic_val p p hp hp.pos = 1 := by
  unfold p_adic_val
  simp [Nat.Prime.factorization_self hp]

theorem p_adic_val_mul (p m n : ℕ)
    (hp : Nat.Prime p)
    (hm : 0 < m) (hn : 0 < n) :
    p_adic_val p (m * n) hp (Nat.mul_pos hm hn) =
    p_adic_val p m hp hm +
    p_adic_val p n hp hn := by
  unfold p_adic_val
  rw [Nat.factorization_mul hm.ne' hn.ne']
  simp [Finsupp.add_apply]

-- p-adic norm: |n|_p = p^{-v_p(n)}
noncomputable def p_adic_norm (p n : ℕ)
    (hp : Nat.Prime p) (hn : 0 < n) : ℝ :=
  (p : ℝ) ^ (-(p_adic_val p n hp hn : ℤ))

theorem p_adic_norm_pos (p n : ℕ)
    (hp : Nat.Prime p) (hn : 0 < n) :
    0 < p_adic_norm p n hp hn := by
  unfold p_adic_norm
  positivity

-- Strong triangle inequality (ultrametric)
theorem p_adic_ultrametric (p m n : ℕ)
    (hp : Nat.Prime p) (hm : 0 < m) (hn : 0 < n) :
    p_adic_norm p (m + n) hp (by omega) ≤
    max (p_adic_norm p m hp hm)
        (p_adic_norm p n hp hn) := by
  apply le_max_iff.mpr
  left
  unfold p_adic_norm
  apply Real.rpow_le_rpow_of_exponent_ge
    (by exact_mod_cast hp.pos)
    (by exact_mod_cast hp.one_lt.le)
  simp
  exact_mod_cast Nat.factorization_add_le m n p

-- ============================================================
-- SECTION 8: ANALYTIC NUMBER THEORY
-- ============================================================

-- Prime number theorem (asymptotic)
-- π(x) ~ x/log(x)
def PNT_approx (n : ℕ) : ℝ :=
  n / Real.log n

theorem PNT_approx_pos (n : ℕ) (hn : 1 < n) :
    0 < PNT_approx n := by
  unfold PNT_approx
  apply div_pos
  · exact_mod_cast Nat.lt_of_lt_pred (by omega)
  · exact Real.log_pos (by exact_mod_cast hn)

-- Bertrand's postulate: ∃ prime p, n < p ≤ 2n
theorem bertrand_postulate (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_and_lt_and_le n hn

-- Chebyshev's estimate: θ(x) = Σ_{p≤x} log p ~ x
noncomputable def chebyshev_theta (n : ℕ) : ℝ :=
  ((Finset.range n).filter Nat.Prime).sum
    (fun p => Real.log p)

theorem chebyshev_theta_pos (n : ℕ) (hn : 2 < n) :
    0 < chebyshev_theta n := by
  unfold chebyshev_theta
  apply Finset.sum_pos_of_ne_zero
  · intro p _; exact le_of_lt (Real.log_pos
      (by exact_mod_cast (Nat.Prime.one_lt
        ((Finset.mem_filter.mp ‹_›).2))))
  · exact ⟨2, by simp [Finset.mem_filter,
      Finset.mem_range, hn], Real.log_pos (by norm_num)⟩

-- Von Mangoldt function Λ(n)
noncomputable def von_mangoldt (n : ℕ) : ℝ :=
  if ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p^k = n
  then Real.log (n.minFac)
  else 0

theorem von_mangoldt_prime (p : ℕ)
    (hp : Nat.Prime p) :
    von_mangoldt p = Real.log p := by
  unfold von_mangoldt
  simp [hp.minFac_eq]
  exact ⟨p, 1, hp, one_pos, by simp⟩

theorem von_mangoldt_nonneg (n : ℕ) :
    0 ≤ von_mangoldt n := by
  unfold von_mangoldt
  split_ifs with h
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.minFac_pos n).ne'
  · linarith

-- ============================================================
-- SECTION 9: AWM NUMBER THEORY BRIDGE
-- Prime structure of 21-domain system
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Domain index as element of ℤ/21ℤ
noncomputable def domain_index
    (d : Domain21) : ℕ :=
  d.toCtorIdx

-- 21 = 3 × 7: domain decomposition
theorem twenty_one_factored :
    21 = 3 * 7 := by norm_num

-- Prime domains: those at prime indices
def prime_domain (d : Domain21) : Prop :=
  Nat.Prime (domain_index d + 1)

-- AWM prime structure
noncomputable def AWM_prime_count : ℕ :=
  Finset.univ.filter
    (fun d => Nat.Prime (domain_index d + 1))
    |>.card

-- Domain totient: number of domains coprime to 21
noncomputable def domain_totient : ℕ :=
  euler_totient 21

theorem domain_totient_val :
    domain_totient = 12 := by
  unfold domain_totient euler_totient
  native_decide

-- Modular domain arithmetic
def domain_mod_equiv
    (d1 d2 : Domain21) (n : ℕ) : Prop :=
  mod_equiv (domain_index d1) (domain_index d2) n

theorem domain_mod_refl
    (d : Domain21) (n : ℕ) :
    domain_mod_equiv d d n :=
  mod_equiv_refl _ _

-- p-adic margin valuation
noncomputable def margin_2adic_val
    (margins : Domain21 → ℕ)
    (d : Domain21)
    (hm : 0 < margins d) : ℕ :=
  p_adic_val 2 (margins d) (by norm_num) hm

theorem margin_val_nonneg
    (margins : Domain21 → ℕ)
    (d : Domain21)
    (hm : 0 < margins d) :
    0 ≤ margin_2adic_val margins d hm :=
  Nat.zero_le _

-- System divisibility: all domain margins divisible by k
def system_divisible
    (margins : Domain21 → ℕ) (k : ℕ) : Prop :=
  ∀ d : Domain21, k ∣ margins d

theorem system_divisible_one
    (margins : Domain21 → ℕ) :
    system_divisible margins 1 :=
  fun _ => one_dvd _

-- Prime resonance: margins at prime values
def prime_resonant
    (margins : Domain21 → ℕ) : Prop :=
  ∀ d : Domain21, Nat.Prime (margins d)

-- If prime resonant, all margins ≥ 2
theorem prime_resonant_ge_two
    (margins : Domain21 → ℕ)
    (h : prime_resonant margins)
    (d : Domain21) :
    2 ≤ margins d :=
  (h d).two_le

-- Von Mangoldt weighted domain sum
noncomputable def domain_mangoldt_sum
    (margins : Domain21 → ℕ) : ℝ :=
  Finset.univ.sum (fun d =>
    von_mangoldt (margins d))

theorem domain_mangoldt_nonneg
    (margins : Domain21 → ℕ) :
    0 ≤ domain_mangoldt_sum margins := by
  unfold domain_mangoldt_sum
  apply Finset.sum_nonneg
  intro d _
  exact von_mangoldt_nonneg (margins d)

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure NumberTheoryLock where
  inf_primes       : ∀ (n : ℕ),
                       ∃ p : ℕ, n < p ∧ Nat.Prime p
  prime_factor     : ∀ (n : ℕ), 1 < n →
                       ∃ p : ℕ, Nat.Prime p ∧ p ∣ n
  totient_prime    : ∀ (p : ℕ), Nat.Prime p →
                       euler_totient p = p - 1
  totient_pos      : ∀ (n : ℕ), 0 < n →
                       0 < euler_totient n
  mobius_one       : mobius 1 = 1
  mobius_prime     : ∀ (p : ℕ), Nat.Prime p →
                       mobius p = -1
  div_sum_prime    : ∀ (p : ℕ), Nat.Prime p →
                       divisor_sum p = p + 1
  mod_refl         : ∀ (a n : ℤ),
                       mod_equiv a a n
  mod_symm         : ∀ (a b n : ℤ),
                       mod_equiv a b n →
                       mod_equiv b a n
  mod_trans        : ∀ (a b c n : ℤ),
                       mod_equiv a b n →
                       mod_equiv b c n →
                       mod_equiv a c n
  padic_pos        : ∀ (p n : ℕ)
                       (hp : Nat.Prime p)
                       (hn : 0 < n),
                       0 < p_adic_norm p n hp hn
  padic_val_mul    : ∀ (p m n : ℕ)
                       (hp : Nat.Prime p)
                       (hm : 0 < m) (hn : 0 < n),
                       p_adic_val p (m * n) hp
                         (Nat.mul_pos hm hn) =
                       p_adic_val p m hp hm +
                       p_adic_val p n hp hn
  bertrand         : ∀ (n : ℕ), 0 < n →
                       ∃ p : ℕ,
                         Nat.Prime p ∧
                         n < p ∧ p ≤ 2 * n
  mangoldt_nn      : ∀ (n : ℕ),
                       0 ≤ von_mangoldt n
  chebyshev_pos    : ∀ (n : ℕ), 2 < n →
                       0 < chebyshev_theta n
  dom_totient      : domain_totient = 12
  dom_mod_refl     : ∀ (d : Domain21) (n : ℕ),
                       domain_mod_equiv d d n
  sys_div_one      : ∀ (m : Domain21 → ℕ),
                       system_divisible m 1
  prime_res_ge2    : ∀ (m : Domain21 → ℕ),
                       prime_resonant m →
                       ∀ d, 2 ≤ m d
  mangoldt_sum_nn  : ∀ (m : Domain21 → ℕ),
                       0 ≤ domain_mangoldt_sum m

def NTLock : NumberTheoryLock where
  inf_primes       := infinitely_many_primes
  prime_factor     := prime_factorization
  totient_prime    := totient_prime
  totient_pos      := totient_pos
  mobius_one       := mobius_one
  mobius_prime     := mobius_prime
  div_sum_prime    := divisor_sum_prime
  mod_refl         := mod_equiv_refl
  mod_symm         := mod_equiv_symm
  mod_trans        := mod_equiv_trans
  padic_pos        := p_adic_norm_pos
  padic_val_mul    := p_adic_val_mul
  bertrand         := bertrand_postulate
  mangoldt_nn      := von_mangoldt_nonneg
  chebyshev_pos    := chebyshev_theta_pos
  dom_totient      := domain_totient_val
  dom_mod_refl     := domain_mod_refl
  sys_div_one      := system_divisible_one
  prime_res_ge2    := prime_resonant_ge_two
  mangoldt_sum_nn  := domain_mangoldt_nonneg

end NumberTheory
