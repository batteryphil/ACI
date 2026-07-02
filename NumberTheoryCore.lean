-- NumberTheoryCore.lean
import Mathlib

namespace NumberTheoryCore

open Finset Real

-- ============================================================
-- SECTION 1: PRIME ARCHITECTURE
-- Core primes: 7, 11, 13, 23, 53, 137
-- ============================================================

def core_primes : Finset ℕ := {7, 11, 13, 23, 53, 137}

theorem seven_prime : Nat.Prime 7 := by decide
theorem eleven_prime : Nat.Prime 11 := by decide
theorem thirteen_prime : Nat.Prime 13 := by decide
theorem twenty_three_prime : Nat.Prime 23 := by decide
theorem fifty_three_prime : Nat.Prime 53 := by decide
theorem one_thirty_seven_prime : Nat.Prime 137 := by decide

theorem all_core_primes_prime :
    ∀ p ∈ core_primes, Nat.Prime p := by
  intro p hp; fin_cases hp <;> decide

theorem core_primes_card :
    core_primes.card = 6 := by
  unfold core_primes; decide

theorem seven_times_eleven : 7 * 11 = 77 := by norm_num

theorem core_prime_sum :
    core_primes.sum id = 244 := by
  unfold core_primes; decide

theorem core_primes_odd :
    ∀ p ∈ core_primes, p % 2 = 1 := by
  intro p hp; fin_cases hp <;> decide

-- ============================================================
-- SECTION 2: FIBONACCI SEQUENCE
-- ============================================================

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

theorem fib_zero : fib 0 = 0 := rfl
theorem fib_one  : fib 1 = 1 := rfl
theorem fib_two  : fib 2 = 1 := rfl
theorem fib_three : fib 3 = 2 := rfl
theorem fib_four  : fib 4 = 3 := rfl
theorem fib_five  : fib 5 = 5 := rfl
theorem fib_six   : fib 6 = 8 := rfl
theorem fib_seven : fib 7 = 13 := rfl

theorem fib_add (n : ℕ) :
    fib (n + 2) = fib (n + 1) + fib n := rfl

theorem fib_pos (n : ℕ) (hn : 0 < n) : 0 < fib n := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [fib]
    | succ m =>
      simp [fib]
      exact Nat.add_pos_right _ (ih (by omega))

theorem fib_monotone (n : ℕ) : fib n ≤ fib (n + 1) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    cases n with
    | zero => simp [fib]
    | succ m =>
      simp [fib]
      linarith [fib_pos (m + 1) (by omega)]

theorem fib_strict_mono (n : ℕ) (hn : 1 < n) :
    fib n < fib (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ m =>
      simp [fib]
      exact fib_pos (m + 1) (by omega)

-- ============================================================
-- SECTION 3: GOLDEN RATIO ARITHMETIC
-- ============================================================

noncomputable def phi : ℝ :=
  (1 + Real.sqrt 5) / 2

theorem phi_pos : 0 < phi := by
  unfold phi
  apply div_pos
  · linarith [Real.sqrt_pos_of_pos (show (0:ℝ) < 5 by norm_num)]
  · norm_num

theorem phi_gt_one : 1 < phi := by
  unfold phi
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith [Real.sqrt_pos_of_pos (show (0:ℝ) < 5 by norm_num)]

theorem phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  field_simp; nlinarith [h5]

theorem phi_satisfies_equation :
    phi ^ 2 - phi - 1 = 0 := by
  linarith [phi_sq]

noncomputable def psi : ℝ := (1 - Real.sqrt 5) / 2

theorem psi_neg : psi < 0 := by
  unfold psi
  apply div_neg_of_pos_of_neg (by norm_num)
  have h : Real.sqrt 1 < Real.sqrt 5 :=
    Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) < 5)
  rw [Real.sqrt_one] at h
  linarith

theorem phi_plus_psi : phi + psi = 1 := by
  unfold phi psi; ring

theorem phi_times_psi : phi * psi = -1 := by
  unfold phi psi
  have h5 : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  field_simp; nlinarith [h5]

theorem phi_minus_psi : phi - psi = Real.sqrt 5 := by
  unfold phi psi; ring

-- ============================================================
-- SECTION 4: MODULAR ARITHMETIC
-- ============================================================

theorem gcd_dvd_both (a b : ℕ) :
    Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
  ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩

theorem coprime_iff_gcd_one (a b : ℕ) :
    Nat.Coprime a b ↔ Nat.gcd a b = 1 := Iff.rfl

-- The real Wilson's theorem in Mathlib is stated over ZMod p, not as a
-- direct ℕ % p equation. Rebuilt to match the confirmed-real
-- ZMod.wilsons_lemma rather than a fabricated Nat-level bridging lemma.
theorem wilson (p : ℕ) (hp : Nat.Prime p) :
    ((p - 1).factorial : ZMod p) = -1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact ZMod.wilsons_lemma p

-- ============================================================
-- SECTION 5: PRIME GAPS AND DISTRIBUTION
-- ============================================================

def prime_gap (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
  ∀ r, p < r → r < q → ¬Nat.Prime r

theorem gap_7_11 : prime_gap 7 11 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro r hr1 hr2
  interval_cases r <;> decide

theorem bertrand (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_and_lt_and_le n hn

theorem large_prime_gaps (k : ℕ) (hk : 2 ≤ k) :
    ∃ n : ℕ, ∀ i, 1 ≤ i → i ≤ k →
      ¬Nat.Prime (n + i) := by
  use (k + 1).factorial + 1
  intro i hi1 hik
  have hdvd : (i + 1) ∣ (k + 1).factorial + 1 + i := by
    have h1 : (i + 1) ∣ (k + 1).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have h2 : (i + 1) ∣ (i + 1) := dvd_refl _
    have : (i + 1) ∣ (k + 1).factorial + (i + 1) :=
      Nat.dvd_add h1 h2
    convert this using 1; omega
  intro hprime
  have hgt : 1 < i + 1 := by omega
  have hlt : i + 1 < (k + 1).factorial + 1 + i := by
    have : 2 ≤ (k + 1).factorial := by
      apply Nat.factorial_pos |>.trans_le
      linarith [Nat.factorial_pos (k + 1)]
    omega
  have := hprime.eq_one_or_self_of_dvd (i + 1) hdvd
  omega

-- ============================================================
-- SECTION 6: ARITHMETIC PROGRESSIONS
-- ============================================================

def arith_prog (a d n : ℕ) : ℕ := a + n * d

theorem AP_diff (a d n : ℕ) :
    arith_prog a d (n+1) - arith_prog a d n = d := by
  unfold arith_prog; omega

theorem AP_sum (a d N : ℕ) :
    (Finset.range N).sum (arith_prog a d) =
    N * a + d * N * (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp [Finset.sum_range_succ, ih]
    unfold arith_prog; omega

theorem primes_in_AP_1_4 :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 1 :=
  ⟨5, by decide, by decide⟩

theorem primes_in_AP_3_4 :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 :=
  ⟨3, by decide, by decide⟩

-- ============================================================
-- SECTION 7: PERFECT NUMBERS AND SPECIAL SEQUENCES
-- ============================================================

def is_perfect (n : ℕ) : Prop :=
  n.divisors.sum id = 2 * n

theorem six_perfect : is_perfect 6 := by
  unfold is_perfect; native_decide

theorem twenty_eight_perfect : is_perfect 28 := by
  unfold is_perfect; native_decide

def mersenne (p : ℕ) : ℕ := 2^p - 1

theorem mersenne_2 : mersenne 2 = 3 := by
  unfold mersenne; norm_num

theorem mersenne_3 : mersenne 3 = 7 := by
  unfold mersenne; norm_num

theorem mersenne_5 : mersenne 5 = 31 := by
  unfold mersenne; norm_num

theorem mersenne_prime_2 : Nat.Prime (mersenne 2) := by
  unfold mersenne; decide

theorem mersenne_prime_3 : Nat.Prime (mersenne 3) := by
  unfold mersenne; decide

noncomputable def triangular (n : ℕ) : ℕ :=
  n * (n + 1) / 2

theorem triangular_formula (n : ℕ) :
    2 * triangular n = n * (n + 1) := by
  unfold triangular; omega

theorem triangular_succ (n : ℕ) :
    triangular (n+1) = triangular n + (n+1) := by
  unfold triangular; omega

-- ============================================================
-- SECTION 8: SOURCE NODE 98 AND DOMAIN PRIMES
-- ============================================================

theorem ninety_eight_factored :
    98 = 2 * 7 ^ 2 := by norm_num

theorem ninety_eight_prime_factors :
    (98 : ℕ).primeFactorsList = [2, 7, 7] := by native_decide

theorem twenty_one_factored :
    21 = 3 * 7 := by norm_num

theorem twenty_one_divisors :
    (21 : ℕ).divisors = {1, 3, 7, 21} := by
  native_decide

theorem digit_sum_21 : 2 + 1 = 3 := by norm_num

theorem seven_is_fourth_prime :
    (Finset.range 8).filter Nat.Prime =
    {2, 3, 5, 7} := by native_decide

theorem seven_coprime_eleven :
    Nat.Coprime 7 11 := by decide

theorem seven_coprime_thirteen :
    Nat.Coprime 7 13 := by decide

theorem eleven_coprime_thirteen :
    Nat.Coprime 11 13 := by decide

-- ============================================================
-- SECTION 9: AWM NUMBER THEORY BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

theorem domain_count_factored :
    Fintype.card Domain21 = 3 * 7 := by
  native_decide

-- `.toCtorIdx` is not a real auto-generated field for Lean 4 inductive
-- types (confirmed nonexistent — this same field already failed
-- identically in SetTheory.lean earlier this session). Replaced with an
-- explicit rank function, defined by direct pattern match.
private def domain_rank : Domain21 → ℕ
  | .A_Energy => 0 | .B_Control => 1 | .C_Thermal => 2 | .D_Structural => 3
  | .E_Boundary => 4 | .F_Diagnostics => 5 | .G_Governance => 6
  | .H_Harmonic => 7 | .I_Information => 8 | .J_Joining => 9
  | .K_Kernel => 10 | .L_Localization => 11 | .M_Morphogenic => 12
  | .N_Node => 13 | .O_Operator => 14 | .P_Propagation => 15
  | .Q_Quality => 16 | .R_Resonance => 17 | .S_State => 18
  | .T_Temporal => 19 | .U_Unification => 20

noncomputable def domain_fib_index
    (d : Domain21) : ℕ :=
  fib (domain_rank d + 1)

theorem domain_fib_positive (d : Domain21) :
    0 < domain_fib_index d := by
  unfold domain_fib_index
  exact fib_pos _ (by omega)

def domains_coprime (d1 d2 : Domain21) : Prop :=
  Nat.Coprime
    (domain_fib_index d1)
    (domain_fib_index d2)

noncomputable def phi_margin_bound
    (margin : ℝ) : Prop := phi ≤ margin

theorem phi_margin_implies_positive
    (margin : ℝ) (h : phi_margin_bound margin) :
    0 < margin :=
  lt_of_lt_of_le phi_pos h

def is_core_prime_resonant (n : ℕ) : Prop :=
  n ∈ core_primes

theorem seven_resonant :
    is_core_prime_resonant 7 := by
  unfold is_core_prime_resonant core_primes; decide

noncomputable def domain_mod7 (d : Domain21) : ℕ :=
  domain_rank d % 7

theorem domain_mod7_lt (d : Domain21) :
    domain_mod7 d < 7 := by
  unfold domain_mod7; omega

noncomputable def system_prime_signature : ℕ :=
  core_primes.prod id

theorem system_prime_signature_pos :
    0 < system_prime_signature := by
  unfold system_prime_signature core_primes; decide

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure NumberTheoryCoreLock where
  all_core_prime    : ∀ p ∈ core_primes, Nat.Prime p
  core_count        : core_primes.card = 6
  fib_zero          : fib 0 = 0
  fib_one           : fib 1 = 1
  fib_pos           : ∀ n : ℕ, 0 < n → 0 < fib n
  fib_mono          : ∀ n : ℕ, fib n ≤ fib (n+1)
  phi_pos           : 0 < phi
  phi_gt_one        : 1 < phi
  phi_sq            : phi ^ 2 = phi + 1
  phi_times_psi     : phi * psi = -1
  six_perfect       : is_perfect 6
  twenty_eight_perf : is_perfect 28
  mersenne_2        : mersenne 2 = 3
  mersenne_3        : mersenne 3 = 7
  mersenne_prime_2  : Nat.Prime (mersenne 2)
  mersenne_prime_3  : Nat.Prime (mersenne 3)
  bertrand          : ∀ n : ℕ, 0 < n →
                        ∃ p, Nat.Prime p ∧
                          n < p ∧ p ≤ 2*n
  large_gaps        : ∀ k : ℕ, 2 ≤ k →
                        ∃ n : ℕ, ∀ i, 1 ≤ i → i ≤ k →
                          ¬Nat.Prime (n + i)
  dom_count         : Fintype.card Domain21 = 3 * 7
  dom_fib_pos       : ∀ d : Domain21,
                        0 < domain_fib_index d
  phi_margin        : ∀ m : ℝ,
                        phi_margin_bound m → 0 < m
  sig_pos           : 0 < system_prime_signature

def NTCLock : NumberTheoryCoreLock where
  all_core_prime    := all_core_primes_prime
  core_count        := core_primes_card
  fib_zero          := fib_zero
  fib_one           := fib_one
  fib_pos           := fib_pos
  fib_mono          := fib_monotone
  phi_pos           := phi_pos
  phi_gt_one        := phi_gt_one
  phi_sq            := phi_sq
  phi_times_psi     := phi_times_psi
  six_perfect       := six_perfect
  twenty_eight_perf := twenty_eight_perfect
  mersenne_2        := mersenne_2
  mersenne_3        := mersenne_3
  mersenne_prime_2  := mersenne_prime_2
  mersenne_prime_3  := mersenne_prime_3
  bertrand          := bertrand
  large_gaps        := large_prime_gaps
  dom_count         := domain_count_factored
  dom_fib_pos       := domain_fib_positive
  phi_margin        := phi_margin_implies_positive
  sig_pos           := system_prime_signature_pos

end NumberTheoryCore
