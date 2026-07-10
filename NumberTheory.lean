import Mathlib

namespace NumberTheory

open Finset Real
open scoped Classical

noncomputable def prime_count (n : ℕ) : ℕ :=
  (Finset.range n).filter Nat.Prime |>.card

theorem prime_count_pos : 0 < prime_count 3 := by
  unfold prime_count; native_decide

theorem prime_count_monotone (m n : ℕ) (h : m ≤ n) :
    prime_count m ≤ prime_count n := by
  unfold prime_count
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono h

theorem infinitely_many_primes :
    ∀ n : ℕ, ∃ p : ℕ, n < p ∧ Nat.Prime p :=
  fun n => (Nat.exists_infinite_primes (n + 1)).imp
    fun p ⟨hp1, hp2⟩ => ⟨by omega, hp2⟩

theorem prime_factorization (n : ℕ) (hn : 1 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ n :=
  ⟨n.minFac, Nat.minFac_prime (by omega),
   Nat.minFac_dvd n⟩

theorem unique_factorization (n : ℕ) (hn : 0 < n) :
    ∃ factors : Multiset ℕ,
      (∀ p ∈ factors, Nat.Prime p) ∧
      factors.prod = n :=
  ⟨(n.primeFactorsList : Multiset ℕ),
   fun p hp => Nat.prime_of_mem_primeFactorsList (Multiset.mem_coe.mp hp),
   by rw [Multiset.prod_coe]; exact Nat.prod_primeFactorsList hn.ne'⟩

def twin_prime_pair (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 2)

theorem twin_prime_exists : twin_prime_pair 5 := by
  constructor <;> decide

def goldbach_property (n : ℕ) : Prop :=
  2 < n → n % 2 = 0 →
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

theorem goldbach_4 : goldbach_property 4 := by
  intro _ _
  exact ⟨2, 2, by decide, by decide, rfl⟩

theorem goldbach_6 : goldbach_property 6 := by
  intro _ _
  exact ⟨3, 3, by decide, by decide, rfl⟩

def mod_equiv (a b n : ℤ) : Prop := n ∣ (a - b)

theorem mod_equiv_refl (a n : ℤ) :
    mod_equiv a a n := by
  unfold mod_equiv; simp

theorem mod_equiv_symm (a b n : ℤ)
    (h : mod_equiv a b n) : mod_equiv b a n := by
  unfold mod_equiv at *
  rwa [show b - a = -(a - b) from by ring, dvd_neg]

theorem mod_equiv_trans (a b c n : ℤ)
    (h1 : mod_equiv a b n) (h2 : mod_equiv b c n) :
    mod_equiv a c n := by
  unfold mod_equiv at *
  have := dvd_add h1 h2
  rwa [show (a - b) + (b - c) = a - c from by ring] at this

theorem mod_equiv_add (a b c d n : ℤ)
    (h1 : mod_equiv a b n) (h2 : mod_equiv c d n) :
    mod_equiv (a + c) (b + d) n := by
  unfold mod_equiv at *
  have := dvd_add h1 h2
  rwa [show (a - b) + (c - d) =
       (a + c) - (b + d) from by ring] at this

theorem mod_equiv_mul (a b c d n : ℤ)
    (h1 : mod_equiv a b n) (h2 : mod_equiv c d n) :
    mod_equiv (a * c) (b * d) n := by
  unfold mod_equiv at *
  have key : n ∣ a * (c - d) + d * (a - b) :=
    dvd_add (dvd_mul_of_dvd_right h2 a)
            (dvd_mul_of_dvd_right h1 d)
  rwa [show a * (c - d) + d * (a - b) =
       a * c - b * d from by ring] at key

theorem wilson (p : ℕ) (hp : Nat.Prime p) :
    (p - 1).factorial % p = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hw := ZMod.wilsons_lemma p
  have h1le : 1 ≤ p := hp.one_lt.le
  have h1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub h1le]
    simp [ZMod.natCast_self]
  have heq : ((p - 1).factorial : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
    rw [hw, h1]
  have hmod : (p - 1).factorial % p = (p - 1) % p :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
  rw [hmod, Nat.mod_eq_of_lt (by omega : p - 1 < p)]

theorem CRT (m n : ℕ) (hcop : Nat.Coprime m n)
    (a b : ℤ) :
    ∃ x : ℤ,
      mod_equiv x a m ∧ mod_equiv x b n := by
  have hbezout : (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [hcop] at h
    exact_mod_cast h.symm
  refine ⟨a * n * Nat.gcdB m n + b * m * Nat.gcdA m n, ?_, ?_⟩
  · exact ⟨Nat.gcdA m n * (b - a), by linear_combination a * hbezout⟩
  · exact ⟨Nat.gcdB m n * (a - b), by linear_combination b * hbezout⟩

noncomputable def legendre_symbol (a p : ℤ) : ℤ :=
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

theorem legendre_one (p : ℤ) (hp : 1 < p) :
    legendre_symbol 1 p = 1 := by
  unfold legendre_symbol
  have hnd : ¬ p ∣ (1 : ℤ) := by
    intro hdvd
    have hle := Int.le_of_dvd one_pos hdvd
    omega
  rw [if_neg hnd, if_pos ⟨1, by unfold mod_equiv; simp⟩]

theorem euler_criterion_sign (p : ℕ)
    (hp : Nat.Prime p) (a : ℤ) :
    legendre_symbol a p = 0 ∨
    legendre_symbol a p = 1 ∨
    legendre_symbol a p = -1 := by
  rcases legendre_values a p with h | h | h <;> simp [h]

theorem legendre_symbol_eq (a p : ℤ) (hp : ¬ p ∣ a)
    (hex : ∃ x : ℤ, mod_equiv (x ^ 2) a p) :
    legendre_symbol a p = 1 := by
  unfold legendre_symbol
  rw [if_neg hp, if_pos hex]

theorem legendre_symbol_eq_neg (a p : ℤ) (hp : ¬ p ∣ a)
    (hex : ¬ ∃ x : ℤ, mod_equiv (x ^ 2) a p) :
    legendre_symbol a p = -1 := by
  unfold legendre_symbol
  rw [if_neg hp, if_neg hex]

theorem not_exists_sq_mod (a : ℤ) (p : ℕ)
    (h : ¬ ∃ y : ZMod p, y ^ 2 = (a : ZMod p)) :
    ¬ ∃ x : ℤ, mod_equiv (x ^ 2) a (p : ℤ) := by
  unfold mod_equiv
  rintro ⟨x, hx⟩
  exact h ⟨(x : ZMod p), by
    have h0 : ((x ^ 2 - a : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hx
    push_cast at h0
    exact sub_eq_zero.mp h0⟩

theorem QR_3_5 :
    legendre_symbol 3 5 * legendre_symbol 5 3 =
    (-1 : ℤ) ^ ((3-1)/2 * ((5-1)/2)) := by
  have e1 : legendre_symbol (3:ℤ) (5:ℤ) = -1 :=
    legendre_symbol_eq_neg 3 5 (by norm_num) (not_exists_sq_mod 3 5 (by decide))
  have e2 : legendre_symbol (5:ℤ) (3:ℤ) = -1 :=
    legendre_symbol_eq_neg 5 3 (by norm_num) (not_exists_sq_mod 5 3 (by decide))
  rw [e1, e2]
  norm_num

theorem QR_3_7 :
    legendre_symbol 3 7 * legendre_symbol 7 3 =
    (-1 : ℤ) ^ ((3-1)/2 * ((7-1)/2)) := by
  have e1 : legendre_symbol (3:ℤ) (7:ℤ) = -1 :=
    legendre_symbol_eq_neg 3 7 (by norm_num) (not_exists_sq_mod 3 7 (by decide))
  have e2 : legendre_symbol (7:ℤ) (3:ℤ) = 1 :=
    legendre_symbol_eq 7 3 (by norm_num) ⟨1, by unfold mod_equiv; norm_num⟩
  rw [e1, e2]
  norm_num

theorem QR_sign (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpp : p % 2 = 1) (hqp : q % 2 = 1)
    (hpq : p ≠ q) :
    (legendre_symbol p q *
     legendre_symbol q p) ^ 2 = 1 := by
  have hne1 : legendre_symbol (p:ℤ) (q:ℤ) ≠ 0 := by
    unfold legendre_symbol
    have hnd : ¬ (q:ℤ) ∣ (p:ℤ) := by
      intro hdvd
      have hqp' : q ∣ p := by exact_mod_cast hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp').symm
    rw [if_neg hnd]
    split_ifs <;> norm_num
  have hne2 : legendre_symbol (q:ℤ) (p:ℤ) ≠ 0 := by
    unfold legendre_symbol
    have hnd : ¬ (p:ℤ) ∣ (q:ℤ) := by
      intro hdvd
      have hpq' : p ∣ q := by exact_mod_cast hdvd
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq')
    rw [if_neg hnd]
    split_ifs <;> norm_num
  have sq1 : legendre_symbol (p:ℤ) (q:ℤ) ^ 2 = 1 := by
    rcases legendre_values (p:ℤ) (q:ℤ) with h|h|h
    · rw [h]; norm_num
    · exact absurd h hne1
    · rw [h]; norm_num
  have sq2 : legendre_symbol (q:ℤ) (p:ℤ) ^ 2 = 1 := by
    rcases legendre_values (q:ℤ) (p:ℤ) with h|h|h
    · rw [h]; norm_num
    · exact absurd h hne2
    · rw [h]; norm_num
  rw [mul_pow, sq1, sq2]
  norm_num

noncomputable def euler_totient (n : ℕ) : ℕ :=
  (Finset.range n).filter
    (fun k => Nat.Coprime k n) |>.card

theorem totient_prime (p : ℕ) (hp : Nat.Prime p) :
    euler_totient p = p - 1 := by
  unfold euler_totient
  have hset : (Finset.range p).filter (fun k => Nat.Coprime k p) =
      Finset.Ico 1 p := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hk, hcop⟩
      refine ⟨?_, hk⟩
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        exact absurd ((Nat.coprime_zero_left p).mp hcop) hp.ne_one
      · exact hk0
    · rintro ⟨hk1, hk2⟩
      refine ⟨hk2, ?_⟩
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdvd
      have := Nat.le_of_dvd hk1 hdvd
      omega
  rw [hset, Nat.card_Ico]

theorem totient_pos (n : ℕ) (hn : 0 < n) :
    0 < euler_totient n := by
  unfold euler_totient
  apply Finset.card_pos.mpr
  rcases eq_or_ne n 1 with hn1 | hn1
  · subst hn1
    exact ⟨0, by simp [Finset.mem_filter, Finset.mem_range, Nat.Coprime]⟩
  · have hn2 : 1 < n := lt_of_le_of_ne hn (Ne.symm hn1)
    exact ⟨1, by simp [Finset.mem_filter, Finset.mem_range, hn2, Nat.Coprime]⟩

noncomputable def mobius (n : ℕ) : ℤ :=
  if n = 1 then 1
  else if ∃ p : ℕ, Nat.Prime p ∧ p^2 ∣ n then 0
  else (-1) ^ (n.primeFactorsList.length)

theorem mobius_one : mobius 1 = 1 := by
  unfold mobius; simp

theorem mobius_prime (p : ℕ) (hp : Nat.Prime p) :
    mobius p = -1 := by
  unfold mobius
  rw [if_neg hp.ne_one]
  have hsq : ¬ ∃ q : ℕ, Nat.Prime q ∧ q ^ 2 ∣ p := by
    rintro ⟨q, hq, hdvd⟩
    have hqp : q ∣ p := (dvd_pow_self q (two_ne_zero)).trans hdvd
    rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h1
    · exact hq.ne_one h1
    · rw [h1] at hdvd
      have hpp : p * p ∣ p := by simpa [sq] using hdvd
      have hple : p * p ≤ p := Nat.le_of_dvd hp.pos hpp
      nlinarith [hp.two_le]
  rw [if_neg hsq, Nat.primeFactorsList_prime hp]
  simp

noncomputable def divisor_sum (n : ℕ) : ℕ :=
  n.divisors.sum id

theorem divisor_sum_prime (p : ℕ) (hp : Nat.Prime p) :
    divisor_sum p = p + 1 := by
  unfold divisor_sum
  rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
  simp only [id_eq]
  omega

def is_multiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧
  ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n

theorem mobius_sq_dvd_iff (m n : ℕ) (hcop : Nat.Coprime m n) :
    (∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ (m * n)) ↔
    (∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ m) ∨ (∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n) := by
  constructor
  · rintro ⟨p, hp, hdvd⟩
    have hpmn : p ∣ m * n := (dvd_pow_self p (two_ne_zero)).trans hdvd
    rcases hp.dvd_mul.mp hpmn with hpm | hpn
    · left
      have hpn' : ¬ p ∣ n := by
        intro hpn
        have hg : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm hpn
        rw [hcop] at hg
        have hle := Nat.le_of_dvd one_pos hg
        have h2le := hp.two_le
        omega
      have hcop_pn : Nat.Coprime (p ^ 2) n := (hp.coprime_iff_not_dvd.mpr hpn').pow_left 2
      exact ⟨p, hp, hcop_pn.dvd_mul_right.mp hdvd⟩
    · right
      have hpm' : ¬ p ∣ m := by
        intro hpm'
        have hg : p ∣ Nat.gcd m n := Nat.dvd_gcd hpm' hpn
        rw [hcop] at hg
        have hle := Nat.le_of_dvd one_pos hg
        have h2le := hp.two_le
        omega
      have hcop_pm : Nat.Coprime (p ^ 2) m := (hp.coprime_iff_not_dvd.mpr hpm').pow_left 2
      exact ⟨p, hp, hcop_pm.dvd_mul_left.mp hdvd⟩
  · rintro (⟨p, hp, hdvd⟩ | ⟨p, hp, hdvd⟩)
    · exact ⟨p, hp, hdvd.trans (dvd_mul_right m n)⟩
    · exact ⟨p, hp, hdvd.trans (dvd_mul_left n m)⟩

theorem mobius_multiplicative :
    is_multiplicative mobius := by
  refine ⟨mobius_one, ?_⟩
  intro m n hcop
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0
    have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hcop
    subst hn1
    simp [mobius]
  rcases eq_or_ne n 0 with hn0 | hn0
  · subst hn0
    have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hcop
    subst hm1
    simp [mobius]
  by_cases hm1 : m = 1
  · subst hm1; simp [mobius_one]
  by_cases hn1 : n = 1
  · subst hn1; simp [mobius_one]
  have hm2 : 2 ≤ m := by omega
  have hn2 : 1 ≤ n := by omega
  have hmn1 : m * n ≠ 1 := by
    have h2 : 2 * 1 ≤ m * n := Nat.mul_le_mul hm2 hn2
    omega
  unfold mobius
  rw [if_neg hmn1, if_neg hm1, if_neg hn1]
  by_cases hsq : (∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ m) ∨ (∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n)
  · rw [if_pos ((mobius_sq_dvd_iff m n hcop).mpr hsq)]
    rcases hsq with h | h
    · rw [if_pos h]; ring
    · rw [if_pos h]; ring
  · have hmnsq : ¬ ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ (m * n) :=
      fun h => hsq ((mobius_sq_dvd_iff m n hcop).mp h)
    have hmsq : ¬ ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ m := fun h => hsq (Or.inl h)
    have hnsq : ¬ ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := fun h => hsq (Or.inr h)
    rw [if_neg hmnsq, if_neg hmsq, if_neg hnsq, ← pow_add]
    congr 1
    have hperm := Nat.perm_primeFactorsList_mul_of_coprime hcop
    rw [hperm.length_eq, List.length_append]

structure DirichletCharacter (q : ℕ) where
  chi      : ℕ → ℂ
  periodic : ∀ n, chi (n + q) = chi n
  chi_one  : chi 1 = 1

noncomputable def zeta_partial (N : ℕ) (s : ℝ)
    (hs : 1 < s) : ℝ :=
  (Finset.range N).sum (fun n =>
    if n = 0 then 0 else 1 / (n : ℝ) ^ s)

theorem zeta_partial_pos (N : ℕ) (s : ℝ)
    (hs : 1 < s) (hN : 1 < N) :
    0 < zeta_partial N s hs := by
  unfold zeta_partial
  apply Finset.sum_pos'
  · intro n _
    split_ifs with h
    · exact le_refl _
    · positivity
  · refine ⟨1, by simp [Finset.mem_range, hN], ?_⟩
    simp only [if_neg (one_ne_zero)]
    positivity

theorem euler_product_2 (s : ℝ) (hs : 1 < s) :
    0 < (1 - (2 : ℝ) ^ (-s))⁻¹ := by
  apply inv_pos.mpr
  have h : (2:ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

def is_algebraic_integer (alpha : ℝ) : Prop :=
  ∃ (n : ℕ) (coeffs : ℕ → ℤ),
    0 < n ∧
    alpha ^ n +
    (Finset.range n).sum (fun i =>
      (coeffs i : ℝ) * alpha ^ i) = 0

theorem integers_are_algebraic (n : ℤ) :
    is_algebraic_integer n :=
  ⟨1, fun _ => -n, one_pos, by simp⟩

theorem sqrt2_algebraic :
    is_algebraic_integer (Real.sqrt 2) := by
  refine ⟨2, fun i => if i = 0 then -2 else 0, by norm_num, ?_⟩
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Finset.sum_range_succ, Finset.sum_range_one, h2]
  norm_num

noncomputable def algebraic_norm
    (alpha : ℝ) (n : ℕ) : ℝ := |alpha| ^ n

theorem algebraic_norm_pos
    (alpha : ℝ) (n : ℕ) (hn : 0 < n)
    (h : alpha ≠ 0) :
    0 < algebraic_norm alpha n :=
  pow_pos (abs_pos.mpr h) n

noncomputable def quad_int_norm
    (a b d : ℤ) : ℤ := a ^ 2 - d * b ^ 2

theorem quad_int_norm_mul
    (a1 b1 a2 b2 d : ℤ) :
    quad_int_norm (a1*a2 + d*b1*b2)
                  (a1*b2 + b1*a2) d =
    quad_int_norm a1 b1 d *
    quad_int_norm a2 b2 d := by
  unfold quad_int_norm; ring

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

noncomputable def p_adic_norm (p n : ℕ)
    (hp : Nat.Prime p) (hn : 0 < n) : ℝ :=
  (p : ℝ) ^ (-(p_adic_val p n hp hn : ℤ))

theorem p_adic_norm_pos (p n : ℕ)
    (hp : Nat.Prime p) (hn : 0 < n) :
    0 < p_adic_norm p n hp hn := by
  unfold p_adic_norm
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp.pos
  positivity

noncomputable def PNT_approx (n : ℕ) : ℝ := n / Real.log n

theorem PNT_approx_pos (n : ℕ) (hn : 1 < n) :
    0 < PNT_approx n := by
  unfold PNT_approx
  apply div_pos
  · have h0 : 0 < n := by omega
    exact_mod_cast h0
  · exact Real.log_pos (by exact_mod_cast hn)

theorem bertrand_postulate (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn.ne'

noncomputable def chebyshev_theta (n : ℕ) : ℝ :=
  ((Finset.range n).filter Nat.Prime).sum
    (fun p => Real.log p)

theorem chebyshev_theta_pos (n : ℕ) (hn : 2 < n) :
    0 < chebyshev_theta n := by
  unfold chebyshev_theta
  apply Finset.sum_pos'
  · intro p hp
    exact le_of_lt (Real.log_pos
      (by exact_mod_cast
        (Finset.mem_filter.mp hp).2.one_lt))
  · exact ⟨2, by simp [Finset.mem_filter,
                Finset.mem_range, hn, Nat.prime_two], Real.log_pos (by norm_num)⟩

noncomputable def von_mangoldt (n : ℕ) : ℝ :=
  if ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p^k = n
  then Real.log (n.minFac)
  else 0

theorem von_mangoldt_prime (p : ℕ)
    (hp : Nat.Prime p) :
    von_mangoldt p = Real.log p := by
  unfold von_mangoldt
  rw [if_pos ⟨p, 1, hp, one_pos, by simp⟩, hp.minFac_eq]

theorem von_mangoldt_nonneg (n : ℕ) :
    0 ≤ von_mangoldt n := by
  unfold von_mangoldt
  split_ifs with h
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.minFac_pos n).ne'
  · linarith

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

def domain_index (d : Domain21) : ℕ := domain_rank d

theorem twenty_one_factored : 21 = 3 * 7 := by norm_num

def prime_domain (d : Domain21) : Prop :=
  Nat.Prime (domain_index d + 1)

noncomputable def domain_totient : ℕ :=
  euler_totient 21

theorem domain_totient_val : domain_totient = 12 := by
  unfold domain_totient euler_totient; native_decide

def domain_mod_equiv
    (d1 d2 : Domain21) (n : ℕ) : Prop :=
  mod_equiv (domain_index d1) (domain_index d2) n

theorem domain_mod_refl (d : Domain21) (n : ℕ) :
    domain_mod_equiv d d n :=
  mod_equiv_refl _ _

noncomputable def margin_2adic_val
    (margins : Domain21 → ℕ) (d : Domain21)
    (hm : 0 < margins d) : ℕ :=
  p_adic_val 2 (margins d) (by norm_num) hm

theorem margin_val_nonneg
    (margins : Domain21 → ℕ) (d : Domain21)
    (hm : 0 < margins d) :
    0 ≤ margin_2adic_val margins d hm :=
  Nat.zero_le _

def system_divisible
    (margins : Domain21 → ℕ) (k : ℕ) : Prop :=
  ∀ d : Domain21, k ∣ margins d

theorem system_divisible_one
    (margins : Domain21 → ℕ) :
    system_divisible margins 1 :=
  fun _ => one_dvd _

def prime_resonant (margins : Domain21 → ℕ) : Prop :=
  ∀ d : Domain21, Nat.Prime (margins d)

theorem prime_resonant_ge_two
    (margins : Domain21 → ℕ)
    (h : prime_resonant margins)
    (d : Domain21) : 2 ≤ margins d :=
  (h d).two_le

noncomputable def domain_mangoldt_sum
    (margins : Domain21 → ℕ) : ℝ :=
  Finset.univ.sum (fun d =>
    von_mangoldt (margins d))

theorem domain_mangoldt_nonneg
    (margins : Domain21 → ℕ) :
    0 ≤ domain_mangoldt_sum margins := by
  unfold domain_mangoldt_sum
  apply Finset.sum_nonneg
  intro d _; exact von_mangoldt_nonneg (margins d)

structure NumberTheoryLock where
  inf_primes      : ∀ (n : ℕ),
                      ∃ p : ℕ, n < p ∧ Nat.Prime p
  prime_factor    : ∀ (n : ℕ), 1 < n →
                      ∃ p : ℕ, Nat.Prime p ∧ p ∣ n
  totient_prime   : ∀ (p : ℕ), Nat.Prime p →
                      euler_totient p = p - 1
  totient_pos     : ∀ (n : ℕ), 0 < n →
                      0 < euler_totient n
  mobius_one      : mobius 1 = 1
  mobius_prime    : ∀ (p : ℕ), Nat.Prime p →
                      mobius p = -1
  mobius_mult     : is_multiplicative mobius
  div_sum_prime   : ∀ (p : ℕ), Nat.Prime p →
                      divisor_sum p = p + 1
  mod_refl        : ∀ (a n : ℤ), mod_equiv a a n
  mod_symm        : ∀ (a b n : ℤ),
                      mod_equiv a b n →
                      mod_equiv b a n
  mod_trans       : ∀ (a b c n : ℤ),
                      mod_equiv a b n →
                      mod_equiv b c n →
                      mod_equiv a c n
  padic_pos       : ∀ (p n : ℕ)
                      (hp : Nat.Prime p) (hn : 0 < n),
                      0 < p_adic_norm p n hp hn
  padic_val_mul   : ∀ (p m n : ℕ)
                      (hp : Nat.Prime p)
                      (hm : 0 < m) (hn : 0 < n),
                      p_adic_val p (m * n) hp
                        (Nat.mul_pos hm hn) =
                      p_adic_val p m hp hm +
                      p_adic_val p n hp hn
  bertrand        : ∀ (n : ℕ), 0 < n →
                      ∃ p : ℕ, Nat.Prime p ∧
                               n < p ∧ p ≤ 2 * n
  mangoldt_nn     : ∀ (n : ℕ), 0 ≤ von_mangoldt n
  chebyshev_pos   : ∀ (n : ℕ), 2 < n →
                      0 < chebyshev_theta n
  dom_totient     : domain_totient = 12
  dom_mod_refl    : ∀ (d : Domain21) (n : ℕ),
                      domain_mod_equiv d d n
  sys_div_one     : ∀ (m : Domain21 → ℕ),
                      system_divisible m 1
  prime_res_ge2   : ∀ (m : Domain21 → ℕ),
                      prime_resonant m →
                      ∀ d, 2 ≤ m d
  mangoldt_sum_nn : ∀ (m : Domain21 → ℕ),
                      0 ≤ domain_mangoldt_sum m

def NTLock : NumberTheoryLock where
  inf_primes      := infinitely_many_primes
  prime_factor    := prime_factorization
  totient_prime   := totient_prime
  totient_pos     := totient_pos
  mobius_one      := mobius_one
  mobius_prime    := mobius_prime
  mobius_mult     := mobius_multiplicative
  div_sum_prime   := divisor_sum_prime
  mod_refl        := mod_equiv_refl
  mod_symm        := mod_equiv_symm
  mod_trans       := mod_equiv_trans
  padic_pos       := p_adic_norm_pos
  padic_val_mul   := p_adic_val_mul
  bertrand        := bertrand_postulate
  mangoldt_nn     := von_mangoldt_nonneg
  chebyshev_pos   := chebyshev_theta_pos
  dom_totient     := domain_totient_val
  dom_mod_refl    := domain_mod_refl
  sys_div_one     := system_divisible_one
  prime_res_ge2   := prime_resonant_ge_two
  mangoldt_sum_nn := domain_mangoldt_nonneg

end NumberTheory
