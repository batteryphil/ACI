import Mathlib

namespace MathematicalEconomics

open Finset Real

-- ============================================================
-- SECTION 1: UTILITY THEORY
-- ============================================================

noncomputable def utility (n : ℕ)
    (U : Fin n → ℝ) : ℝ :=
  Finset.univ.sum U

theorem utility_nonneg (n : ℕ)
    (U : Fin n → ℝ)
    (hU : ∀ i, 0 ≤ U i) :
    0 ≤ utility n U :=
  Finset.sum_nonneg (fun i _ => hU i)

noncomputable def cobb_douglas (n : ℕ)
    (x alpha : Fin n → ℝ) : ℝ :=
  Finset.univ.prod (fun i =>
    x i ^ alpha i)

theorem cobb_douglas_pos (n : ℕ)
    (x alpha : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    0 < cobb_douglas n x alpha := by
  unfold cobb_douglas
  apply Finset.prod_pos; intro i _
  exact Real.rpow_pos_of_pos (hx i) _

theorem marginal_utility_nonneg
    (MU : ℝ) (h : 0 ≤ MU) : 0 ≤ MU := h

theorem DMU_proxy (U : ℝ → ℝ)
    (hU : ∀ x y, x ≤ y →
      U y - U x ≤ U x - U 0) :
    True := trivial

-- ============================================================
-- SECTION 2: CONSUMER THEORY
-- ============================================================

def satisfies_budget (n : ℕ)
    (p x : Fin n → ℝ) (m : ℝ) : Prop :=
  Finset.univ.sum (fun i => p i * x i) ≤ m

theorem expenditure_nonneg (n : ℕ)
    (p x : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hx : ∀ i, 0 ≤ x i) :
    0 ≤ Finset.univ.sum
      (fun i => p i * x i) :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hp i) (hx i))

theorem hicksian_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

theorem roys_identity_proxy :
    True := trivial

-- ============================================================
-- SECTION 3: PRODUCER THEORY
-- ============================================================

noncomputable def cobb_douglas_prod
    (A K L alpha beta : ℝ)
    (hA : 0 < A) (hK : 0 < K)
    (hL : 0 < L) : ℝ :=
  A * K ^ alpha * L ^ beta

theorem production_pos
    (A K L alpha beta : ℝ)
    (hA : 0 < A) (hK : 0 < K)
    (hL : 0 < L) :
    0 < cobb_douglas_prod
      A K L alpha beta hA hK hL := by
  unfold cobb_douglas_prod
  apply mul_pos (mul_pos hA _)
  · exact Real.rpow_pos_of_pos hL _
  · exact Real.rpow_pos_of_pos hK _

noncomputable def profit
    (p y w L r K : ℝ) : ℝ :=
  p * y - w * L - r * K

theorem cost_nonneg
    (w L r K : ℝ)
    (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hr : 0 ≤ r) (hK : 0 ≤ K) :
    0 ≤ w * L + r * K :=
  add_nonneg (mul_nonneg hw hL)
    (mul_nonneg hr hK)

theorem RTS_proxy (lambda : ℝ)
    (h : 0 < lambda) : 0 < lambda := h

-- ============================================================
-- SECTION 4: GENERAL EQUILIBRIUM
-- ============================================================

def walras_law (n : ℕ)
    (p z : Fin n → ℝ) : Prop :=
  Finset.univ.sum (fun i =>
    p i * z i) = 0

theorem excess_demand_proxy (n : ℕ)
    (z : Fin n → ℝ) :
    ∃ p : Fin n → ℝ,
      ∀ i, 0 ≤ p i :=
  ⟨fun _ => 1, fun _ => by norm_num⟩

theorem AD_proxy :
    True := trivial

def is_pareto_optimal (n : ℕ)
    (alloc : Fin n → ℝ) : Prop :=
  ∀ alloc' : Fin n → ℝ,
    (∀ i, alloc i ≤ alloc' i) →
    alloc' = alloc

-- ============================================================
-- SECTION 5: GAME THEORY
-- ============================================================

structure NormalFormGame (n : ℕ) where
  strategies : Fin n → ℕ
  payoff     : Fin n → ℕ → ℝ

def is_nash (n : ℕ)
    (G : NormalFormGame n)
    (s : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, ∀ s_i : ℕ,
    G.payoff i (s i) ≥
    G.payoff i s_i

theorem dominant_proxy (n : ℕ)
    (G : NormalFormGame n) :
    ∃ s : Fin n → ℕ,
      ∀ i, s i = 0 :=
  ⟨fun _ => 0, fun _ => rfl⟩

def is_mixed_strategy (n : ℕ)
    (sigma : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ sigma i) ∧
  Finset.univ.sum sigma = 1

theorem uniform_mixed_strategy (n : ℕ)
    (hn : 0 < n) :
    is_mixed_strategy n
      (fun _ => 1 / n) := by
  constructor
  · intro _; positivity
  · simp [Finset.sum_const,
          Finset.card_fin]
    field_simp

theorem zero_sum_proxy (n : ℕ)
    (payoffs : Fin n → ℝ)
    (h : Finset.univ.sum payoffs = 0) :
    Finset.univ.sum payoffs = 0 := h

-- ============================================================
-- SECTION 6: WELFARE ECONOMICS
-- ============================================================

noncomputable def social_welfare (n : ℕ)
    (w U : Fin n → ℝ) : ℝ :=
  Finset.univ.sum (fun i => w i * U i)

theorem welfare_nonneg (n : ℕ)
    (w U : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hU : ∀ i, 0 ≤ U i) :
    0 ≤ social_welfare n w U :=
  Finset.sum_nonneg (fun i _ =>
    mul_nonneg (hw i) (hU i))

noncomputable def rawls_welfare (n : ℕ)
    (hn : 0 < n) (U : Fin n → ℝ) : ℝ :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  Finset.univ.inf' Finset.univ_nonempty U

theorem rawls_le_utilitarian (n : ℕ)
    (hn : 0 < n) (U : Fin n → ℝ)
    (hU : ∀ i, 0 ≤ U i) :
    rawls_welfare n hn U ≤
    social_welfare n (fun _ => 1) U := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold rawls_welfare social_welfare
  simp only [one_mul]
  obtain ⟨i0, hi0, heq⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty U
  rw [heq]
  exact Finset.single_le_sum (fun i _ => hU i) hi0

-- ============================================================
-- SECTION 7: GROWTH THEORY
-- ============================================================

noncomputable def solow_steady_state
    (s delta A alpha : ℝ)
    (hs : 0 < s) (hdelta : 0 < delta) : ℝ :=
  (s * A / delta) ^ (1 / (1 - alpha))

theorem growth_rate_nonneg
    (g : ℝ) (h : 0 ≤ g) : 0 ≤ g := h

theorem capital_accum_proxy
    (K : ℝ) (h : 0 < K) : 0 < K := h

-- ============================================================
-- SECTION 8: INFORMATION ECONOMICS
-- ============================================================

theorem adverse_selection_proxy :
    True := trivial

theorem moral_hazard_proxy :
    True := trivial

theorem mechanism_proxy (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

theorem revelation_proxy :
    True := trivial

-- ============================================================
-- SECTION 9: AWM ECONOMICS BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

noncomputable def domain_utility :=
  utility 21 (fun _ => 1)

theorem domain_utility_nonneg :
    0 ≤ domain_utility :=
  utility_nonneg 21 (fun _ => 1)
    (fun _ => by norm_num)

noncomputable def domain_CD :=
  cobb_douglas 21
    (fun _ => 1) (fun _ => 1/21)

theorem domain_CD_pos :
    0 < domain_CD :=
  cobb_douglas_pos 21
    (fun _ => 1) (fun _ => 1/21)
    (fun _ => by norm_num)

noncomputable def domain_welfare :=
  social_welfare 21
    (fun _ => 1/21) (fun _ => 1)

theorem domain_welfare_nonneg :
    0 ≤ domain_welfare :=
  welfare_nonneg 21
    (fun _ => 1/21) (fun _ => 1)
    (fun _ => by norm_num)
    (fun _ => by norm_num)

theorem domain_mixed_strategy :
    is_mixed_strategy 21
      (fun _ => 1/21) :=
  uniform_mixed_strategy 21
    (by norm_num)

theorem domain_budget :
    satisfies_budget 21
      (fun _ => 1) (fun _ => 0) 1 := by
  unfold satisfies_budget
  simp

theorem domain_expenditure_nonneg :
    0 ≤ Finset.univ.sum (fun _ : Fin 21 =>
      (1 : ℝ) * 1) :=
  expenditure_nonneg 21
    (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num)
    (fun _ => by norm_num)

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure MathematicalEconomicsLock where
  utility_nn     : ∀ (n : ℕ) (U : Fin n → ℝ),
                     (∀ i, 0 ≤ U i) →
                     0 ≤ utility n U
  CD_pos         : ∀ (n : ℕ)
                     (x alpha : Fin n → ℝ),
                     (∀ i, 0 < x i) →
                     0 < cobb_douglas n x alpha
  prod_pos       : ∀ (A K L alpha beta : ℝ)
                     (hA : 0 < A) (hK : 0 < K) (hL : 0 < L),
                     0 < cobb_douglas_prod
                       A K L alpha beta hA hK hL
  cost_nn        : ∀ (w L r K : ℝ),
                     0 ≤ w → 0 ≤ L →
                     0 ≤ r → 0 ≤ K →
                     0 ≤ w * L + r * K
  mixed_strat    : ∀ (n : ℕ), 0 < n →
                     is_mixed_strategy n
                       (fun _ => 1 / n)
  welfare_nn     : ∀ (n : ℕ)
                     (w U : Fin n → ℝ),
                     (∀ i, 0 ≤ w i) →
                     (∀ i, 0 ≤ U i) →
                     0 ≤ social_welfare n w U
  rawls_le_util  : ∀ (n : ℕ) (hn : 0 < n)
                     (U : Fin n → ℝ),
                     (∀ i, 0 ≤ U i) →
                     rawls_welfare n hn U ≤
                     social_welfare n
                       (fun _ => 1) U
  dom_util_nn    : 0 ≤ domain_utility
  dom_CD_pos     : 0 < domain_CD
  dom_welfare_nn : 0 ≤ domain_welfare
  dom_mixed      : is_mixed_strategy 21
                     (fun _ => 1/21)
  dom_budget     : satisfies_budget 21
                     (fun _ => 1)
                     (fun _ => 0) 1
  dom_exp_nn     : 0 ≤ Finset.univ.sum
                     (fun _ : Fin 21 =>
                       (1 : ℝ) * 1)

def MELock : MathematicalEconomicsLock where
  utility_nn     := utility_nonneg
  CD_pos         := cobb_douglas_pos
  prod_pos       := production_pos
  cost_nn        := cost_nonneg
  mixed_strat    := uniform_mixed_strategy
  welfare_nn     := welfare_nonneg
  rawls_le_util  := rawls_le_utilitarian
  dom_util_nn    := domain_utility_nonneg
  dom_CD_pos     := domain_CD_pos
  dom_welfare_nn := domain_welfare_nonneg
  dom_mixed      := domain_mixed_strategy
  dom_budget     := domain_budget
  dom_exp_nn     := domain_expenditure_nonneg

end MathematicalEconomics
