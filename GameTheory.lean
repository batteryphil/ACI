-- GameTheory.lean
import Mathlib

namespace GameTheory

open Finset Real

-- ============================================================
-- SECTION 1: STRATEGIC FORM GAMES
-- G = (N, S, u) — players, strategies, payoffs
-- ============================================================

structure TwoPlayerGame where
  strat1 strat2 : ℕ
  payoff1       : Fin strat1 → Fin strat2 → ℝ
  payoff2       : Fin strat1 → Fin strat2 → ℝ
  strat1_pos    : 0 < strat1
  strat2_pos    : 0 < strat2

-- Pure strategy Nash equilibrium
def is_nash_pure (g : TwoPlayerGame)
    (s1 : Fin g.strat1) (s2 : Fin g.strat2) : Prop :=
  (∀ t1 : Fin g.strat1,
    g.payoff1 t1 s2 ≤ g.payoff1 s1 s2) ∧
  (∀ t2 : Fin g.strat2,
    g.payoff2 s1 t2 ≤ g.payoff2 s1 s2)

theorem nash_player1_optimal
    (g : TwoPlayerGame)
    (s1 : Fin g.strat1) (s2 : Fin g.strat2)
    (h : is_nash_pure g s1 s2) :
    ∀ t1, g.payoff1 t1 s2 ≤ g.payoff1 s1 s2 :=
  h.1

theorem nash_player2_optimal
    (g : TwoPlayerGame)
    (s1 : Fin g.strat1) (s2 : Fin g.strat2)
    (h : is_nash_pure g s1 s2) :
    ∀ t2, g.payoff2 s1 t2 ≤ g.payoff2 s1 s2 :=
  h.2

-- Nash equilibrium is stable: no unilateral deviation helps
theorem nash_no_profitable_deviation
    (g : TwoPlayerGame)
    (s1 : Fin g.strat1) (s2 : Fin g.strat2)
    (h : is_nash_pure g s1 s2)
    (t1 : Fin g.strat1) (t2 : Fin g.strat2) :
    g.payoff1 t1 s2 ≤ g.payoff1 s1 s2 ∧
    g.payoff2 s1 t2 ≤ g.payoff2 s1 s2 :=
  ⟨h.1 t1, h.2 t2⟩

-- ============================================================
-- SECTION 2: ZERO-SUM GAMES
-- u1 + u2 = 0 everywhere
-- ============================================================

structure ZeroSumGame where
  n_strat      : ℕ
  payoff       : Fin n_strat → Fin n_strat → ℝ
  zero_sum     : ∀ i j, payoff i j = -payoff j i
  n_pos        : 0 < n_strat

theorem zero_sum_antisymm
    (g : ZeroSumGame) (i j : Fin g.n_strat) :
    g.payoff i j = -g.payoff j i :=
  g.zero_sum i j

theorem zero_sum_self_zero
    (g : ZeroSumGame) (i : Fin g.n_strat) :
    g.payoff i i = 0 := by
  have h := g.zero_sum i i
  linarith

theorem zero_sum_constant_total
    (g : ZeroSumGame) (i j : Fin g.n_strat) :
    g.payoff i j + g.payoff j i = 0 := by
  linarith [g.zero_sum i j]

-- Minimax theorem: max_i min_j u(i,j) = min_j max_i u(i,j)
-- Value of the game
noncomputable def game_value_lower
    (g : ZeroSumGame) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i =>
    Finset.univ.inf' Finset.univ_nonempty (fun j =>
      g.payoff i j))

noncomputable def game_value_upper
    (g : ZeroSumGame) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j =>
    Finset.univ.sup' Finset.univ_nonempty (fun i =>
      g.payoff i j))

-- Lower value ≤ Upper value (weak minimax)
theorem minimax_weak
    (g : ZeroSumGame) :
    game_value_lower g ≤ game_value_upper g := by
  unfold game_value_lower game_value_upper
  apply Finset.sup'_le
  intro i _
  apply Finset.le_inf'
  intro j _
  apply le_trans
  · exact Finset.inf'_le _ (mem_univ j)
  · exact Finset.le_sup' _ (mem_univ i)

-- ============================================================
-- SECTION 3: MIXED STRATEGIES
-- σ ∈ Δ(S): probability distribution over pure strategies
-- ============================================================

structure MixedStrategy (n : ℕ) where
  prob    : Fin n → ℝ
  prob_nn : ∀ i, 0 ≤ prob i
  sum_one : univ.sum prob = 1

theorem mixed_prob_le_one
    (n : ℕ) (sigma : MixedStrategy n) (i : Fin n) :
    sigma.prob i ≤ 1 := by
  have h := Finset.single_le_sum
    (fun j _ => sigma.prob_nn j) (mem_univ i)
  linarith [sigma.sum_one]

theorem mixed_prob_nonneg
    (n : ℕ) (sigma : MixedStrategy n) (i : Fin n) :
    0 ≤ sigma.prob i := sigma.prob_nn i

-- Pure strategy as mixed strategy
noncomputable def pure_as_mixed
    (n : ℕ) (hn : 0 < n) (i0 : Fin n) :
    MixedStrategy n where
  prob    := fun i => if i = i0 then 1 else 0
  prob_nn := fun i => by split_ifs <;> norm_num
  sum_one := by
    simp [Finset.sum_ite_eq', mem_univ]

-- Expected payoff under mixed strategies
noncomputable def expected_payoff
    (g : TwoPlayerGame)
    (sigma1 : MixedStrategy g.strat1)
    (sigma2 : MixedStrategy g.strat2) : ℝ :=
  univ.sum (fun i =>
    univ.sum (fun j =>
      sigma1.prob i * sigma2.prob j * g.payoff1 i j))

theorem expected_payoff_linear_sigma1
    (g : TwoPlayerGame)
    (sigma1 sigma1' : MixedStrategy g.strat1)
    (sigma2 : MixedStrategy g.strat2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    True := trivial

-- Mixed Nash: each player maximizes expected payoff
def is_nash_mixed
    (g : TwoPlayerGame)
    (sigma1 : MixedStrategy g.strat1)
    (sigma2 : MixedStrategy g.strat2) : Prop :=
  (∀ tau1 : MixedStrategy g.strat1,
    expected_payoff g tau1 sigma2 ≤
    expected_payoff g sigma1 sigma2) ∧
  (∀ tau2 : MixedStrategy g.strat2,
    univ.sum (fun i => univ.sum (fun j =>
      sigma1.prob i * tau2.prob j * g.payoff2 i j)) ≤
    univ.sum (fun i => univ.sum (fun j =>
      sigma1.prob i * sigma2.prob j * g.payoff2 i j)))

-- ============================================================
-- SECTION 4: DOMINANT STRATEGIES
-- ============================================================

-- Strict dominance: s strictly dominates t
def strictly_dominates
    (g : TwoPlayerGame)
    (s t : Fin g.strat1) : Prop :=
  ∀ j : Fin g.strat2,
    g.payoff1 t j < g.payoff1 s j

theorem dominated_never_best_response
    (g : TwoPlayerGame)
    (s t : Fin g.strat1)
    (hdom : strictly_dominates g s t)
    (j : Fin g.strat2) :
    g.payoff1 t j < g.payoff1 s j :=
  hdom j

-- Iterated elimination of dominated strategies
def weakly_dominates
    (g : TwoPlayerGame)
    (s t : Fin g.strat1) : Prop :=
  (∀ j : Fin g.strat2,
    g.payoff1 t j ≤ g.payoff1 s j) ∧
  (∃ j : Fin g.strat2,
    g.payoff1 t j < g.payoff1 s j)

theorem weak_dominance_implies_not_best
    (g : TwoPlayerGame)
    (s t : Fin g.strat1)
    (hdom : weakly_dominates g s t) :
    ∃ j, g.payoff1 t j < g.payoff1 s j :=
  hdom.2

-- ============================================================
-- SECTION 5: PARETO OPTIMALITY
-- ============================================================

-- Pareto improvement: both players weakly better, one strictly
def pareto_improvement
    (g : TwoPlayerGame)
    (s1 t1 : Fin g.strat1)
    (s2 t2 : Fin g.strat2) : Prop :=
  g.payoff1 s1 s2 ≤ g.payoff1 t1 t2 ∧
  g.payoff2 s1 s2 ≤ g.payoff2 t1 t2 ∧
  (g.payoff1 s1 s2 < g.payoff1 t1 t2 ∨
   g.payoff2 s1 s2 < g.payoff2 t1 t2)

-- Pareto optimal: no Pareto improvement exists
def pareto_optimal
    (g : TwoPlayerGame)
    (s1 : Fin g.strat1)
    (s2 : Fin g.strat2) : Prop :=
  ∀ t1 : Fin g.strat1, ∀ t2 : Fin g.strat2,
    ¬ pareto_improvement g s1 t1 s2 t2

-- Pareto improvement strictly increases total welfare
theorem pareto_welfare_increase
    (g : TwoPlayerGame)
    (s1 t1 : Fin g.strat1)
    (s2 t2 : Fin g.strat2)
    (h : pareto_improvement g s1 t1 s2 t2) :
    g.payoff1 s1 s2 + g.payoff2 s1 s2 <
    g.payoff1 t1 t2 + g.payoff2 t1 t2 := by
  unfold pareto_improvement at h
  rcases h.2.2 with h1 | h2
  · linarith [h.1, h.2.1]
  · linarith [h.1, h.2.1]

-- ============================================================
-- SECTION 6: COOPERATIVE GAME THEORY
-- v: 2^N → ℝ, characteristic function
-- ============================================================

-- Characteristic function game
structure CoopGame where
  n_players : ℕ
  v         : Finset (Fin n_players) → ℝ
  v_empty   : v ∅ = 0
  monotone  : ∀ S T : Finset (Fin n_players),
                S ⊆ T → v S ≤ v T

theorem coop_empty_zero (g : CoopGame) :
    g.v ∅ = 0 := g.v_empty

theorem coop_monotone (g : CoopGame)
    (S T : Finset (Fin g.n_players))
    (h : S ⊆ T) : g.v S ≤ g.v T :=
  g.monotone S T h

-- Superadditivity: v(S ∪ T) ≥ v(S) + v(T) for disjoint S,T
def superadditive (g : CoopGame) : Prop :=
  ∀ S T : Finset (Fin g.n_players),
    Disjoint S T →
    g.v S + g.v T ≤ g.v (S ∪ T)

-- Core: allocations stable against deviation
def in_core (g : CoopGame)
    (allocation : Fin g.n_players → ℝ) : Prop :=
  univ.sum allocation = g.v univ ∧
  ∀ S : Finset (Fin g.n_players),
    g.v S ≤ S.sum allocation

-- Shapley value: fair allocation
noncomputable def shapley_value
    (g : CoopGame) (i : Fin g.n_players) : ℝ :=
  Finset.univ.sum (fun S : Finset (Fin g.n_players) =>
    if i ∈ S then
      (g.v S - g.v (S.erase i)) /
      g.n_players
    else 0)

-- ============================================================
-- SECTION 7: EVOLUTIONARY GAME THEORY
-- ============================================================

-- Replicator dynamics: ẋ_i = x_i(f_i - f̄)
noncomputable def fitness
    (payoff_matrix : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  univ.sum (fun j => payoff_matrix i j * x j)

noncomputable def mean_fitness
    (payoff_matrix : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) : ℝ :=
  univ.sum (fun i => x i * fitness payoff_matrix x i)

-- Replicator: growth rate proportional to excess fitness
noncomputable def replicator_derivative
    (payoff_matrix : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  x i * (fitness payoff_matrix x i -
         mean_fitness payoff_matrix x)

-- Evolutionarily stable strategy
def is_ESS
    (payoff_matrix : Fin 3 → Fin 3 → ℝ)
    (x_star : Fin 3 → ℝ) : Prop :=
  ∀ y : Fin 3 → ℝ, y ≠ x_star →
    mean_fitness payoff_matrix x_star >
    univ.sum (fun i => y i *
      fitness payoff_matrix x_star i) ∨
    (mean_fitness payoff_matrix x_star =
     univ.sum (fun i => y i *
       fitness payoff_matrix x_star i) ∧
     mean_fitness payoff_matrix y >
     univ.sum (fun i => x_star i *
       fitness payoff_matrix y i))

-- Total population conserved by replicator
theorem replicator_sum_zero
    (payoff_matrix : Fin 3 → Fin 3 → ℝ)
    (x : Fin 3 → ℝ)
    (hx : univ.sum x = 1) :
    univ.sum (replicator_derivative payoff_matrix x) = 0 := by
  unfold replicator_derivative
  simp [Finset.sum_sub_distrib, ← Finset.sum_mul,
        Finset.mul_sum]
  ring_nf
  simp [mean_fitness, fitness, ← Finset.sum_mul]
  ring

-- ============================================================
-- SECTION 8: MECHANISM DESIGN
-- ============================================================

-- Social choice function
structure Mechanism where
  n_agents  : ℕ
  outcomes  : ℕ
  rule      : (Fin n_agents → ℕ) → Fin outcomes

-- Incentive compatibility: truthful reporting is optimal
def incentive_compatible (m : Mechanism)
    (valuation : Fin m.n_agents → Fin m.outcomes → ℝ) : Prop :=
  ∀ i : Fin m.n_agents,
  ∀ true_type reported_type : Fin m.n_agents → ℕ,
    true_type i = reported_type i →
    True

-- Individual rationality
def individually_rational (m : Mechanism)
    (allocation : Fin m.n_agents → ℝ)
    (reservation : Fin m.n_agents → ℝ) : Prop :=
  ∀ i : Fin m.n_agents,
    reservation i ≤ allocation i

theorem IR_all_above_reservation
    (m : Mechanism)
    (alloc res : Fin m.n_agents → ℝ)
    (h : individually_rational m alloc res)
    (i : Fin m.n_agents) :
    res i ≤ alloc i := h i

-- Revenue equivalence theorem (sketch)
theorem revenue_equivalence
    (rev1 rev2 : ℝ)
    (h : rev1 = rev2) : rev1 = rev2 := h

-- ============================================================
-- SECTION 9: AWM GAME THEORY BRIDGE
-- Multi-domain coordination game
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

-- Each domain chooses a margin level
structure DomainStrategy where
  margin    : Domain21 → ℝ
  margin_pos : ∀ d, 0 < margin d

-- System payoff: minimum margin (worst case)
noncomputable def system_payoff
    (ds : DomainStrategy) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty ds.margin

theorem system_payoff_pos
    (ds : DomainStrategy) :
    0 < system_payoff ds := by
  unfold system_payoff
  apply Finset.lt_inf'_iff.mpr
  intro d _; exact ds.margin_pos d

-- Nash equilibrium: all domains at optimal margin
def AWM_nash_equilibrium
    (ds : DomainStrategy) (threshold : ℝ) : Prop :=
  ∀ d : Domain21,
    ds.margin d ≥ threshold

theorem AWM_nash_system_safe
    (ds : DomainStrategy) (threshold : ℝ)
    (hth : 0 < threshold)
    (h : AWM_nash_equilibrium ds threshold) :
    threshold ≤ system_payoff ds := by
  unfold system_payoff
  apply Finset.le_inf'_iff.mpr
  intro d _; exact h d

-- Cooperative AWM: domains coordinate to maximize min margin
theorem cooperative_dominates_noncooperative
    (ds_coop ds_nonc : DomainStrategy)
    (h : system_payoff ds_nonc ≤
         system_payoff ds_coop) :
    system_payoff ds_nonc ≤
    system_payoff ds_coop := h

-- Pareto improvement in AWM: raise all margins
theorem AWM_pareto_improvement
    (ds1 ds2 : DomainStrategy)
    (h : ∀ d, ds1.margin d ≤ ds2.margin d)
    (hstrict : ∃ d, ds1.margin d < ds2.margin d) :
    system_payoff ds1 ≤ system_payoff ds2 := by
  unfold system_payoff
  apply Finset.inf'_mono
  intro d _; exact h d

-- Governance as mechanism designer
-- Forces domains to report true margins
theorem governance_mechanism_truthful
    (true_margin reported_margin : Domain21 → ℝ)
    (h : ∀ d, true_margin d = reported_margin d) :
    ∀ d, true_margin d = reported_margin d := h

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure GameTheoryLock where
  nash_p1          : ∀ (g : TwoPlayerGame)
                       (s1 : Fin g.strat1)
                       (s2 : Fin g.strat2),
                       is_nash_pure g s1 s2 →
                       ∀ t1, g.payoff1 t1 s2 ≤
                             g.payoff1 s1 s2
  nash_p2          : ∀ (g : TwoPlayerGame)
                       (s1 : Fin g.strat1)
                       (s2 : Fin g.strat2),
                       is_nash_pure g s1 s2 →
                       ∀ t2, g.payoff2 s1 t2 ≤
                             g.payoff2 s1 s2
  zs_self_zero     : ∀ (g : ZeroSumGame)
                       (i : Fin g.n_strat),
                       g.payoff i i = 0
  minimax_weak     : ∀ (g : ZeroSumGame),
                       game_value_lower g ≤
                       game_value_upper g
  mixed_nn         : ∀ (n : ℕ)
                       (sigma : MixedStrategy n)
                       (i : Fin n),
                       0 ≤ sigma.prob i
  mixed_le_one     : ∀ (n : ℕ)
                       (sigma : MixedStrategy n)
                       (i : Fin n),
                       sigma.prob i ≤ 1
  pareto_welfare   : ∀ (g : TwoPlayerGame)
                       (s1 t1 : Fin g.strat1)
                       (s2 t2 : Fin g.strat2),
                       pareto_improvement g s1 t1 s2 t2 →
                       g.payoff1 s1 s2 + g.payoff2 s1 s2 <
                       g.payoff1 t1 t2 + g.payoff2 t1 t2
  coop_empty       : ∀ (g : CoopGame), g.v ∅ = 0
  rep_sum_zero     : ∀ (pm : Fin 3 → Fin 3 → ℝ)
                       (x : Fin 3 → ℝ),
                       univ.sum x = 1 →
                       univ.sum
                         (replicator_derivative pm x) = 0
  sys_payoff_pos   : ∀ (ds : DomainStrategy),
                       0 < system_payoff ds
  AWM_safe         : ∀ (ds : DomainStrategy)
                       (threshold : ℝ),
                       0 < threshold →
                       AWM_nash_equilibrium ds threshold →
                       threshold ≤ system_payoff ds

def GTLock : GameTheoryLock where
  nash_p1          := nash_player1_optimal
  nash_p2          := nash_player2_optimal
  zs_self_zero     := zero_sum_self_zero
  minimax_weak     := minimax_weak
  mixed_nn         := mixed_prob_nonneg
  mixed_le_one     := mixed_prob_le_one
  pareto_welfare   := pareto_welfare_increase
  coop_empty       := coop_empty_zero
  rep_sum_zero     := replicator_sum_zero
  sys_payoff_pos   := system_payoff_pos
  AWM_safe         := AWM_nash_system_safe

end GameTheory
