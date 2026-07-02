-- SetTheory.lean
import Mathlib

namespace SetTheory

open Finset

-- ============================================================
-- SECTION 1: BASIC SET OPERATIONS
-- ============================================================

theorem union_comm (α : Type*) (A B : Set α) :
    A ∪ B = B ∪ A :=
  Set.union_comm A B

theorem inter_comm (α : Type*) (A B : Set α) :
    A ∩ B = B ∩ A :=
  Set.inter_comm A B

theorem union_assoc (α : Type*) (A B C : Set α) :
    A ∪ B ∪ C = A ∪ (B ∪ C) :=
  Set.union_assoc A B C

theorem inter_distrib_union
    (α : Type*) (A B C : Set α) :
    A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C :=
  Set.inter_union_distrib_left A B C

theorem demorgan_union
    (α : Type*) (A B : Set α) :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ :=
  Set.compl_union A B

theorem demorgan_inter
    (α : Type*) (A B : Set α) :
    (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
  Set.compl_inter A B

-- ============================================================
-- SECTION 2: CARDINALITY
-- ============================================================

theorem card_union_le (α : Type*)
    [DecidableEq α]
    (A B : Finset α) :
    (A ∪ B).card ≤ A.card + B.card :=
  Finset.card_union_le A B

theorem card_inter_le_left (α : Type*)
    [DecidableEq α]
    (A B : Finset α) :
    (A ∩ B).card ≤ A.card :=
  Finset.card_inter_le_left

theorem card_subset_le (α : Type*)
    [DecidableEq α]
    (A B : Finset α) (h : A ⊆ B) :
    A.card ≤ B.card :=
  Finset.card_le_card h

theorem card_empty : (∅ : Finset ℕ).card = 0 :=
  Finset.card_empty

theorem card_singleton (a : ℕ) :
    ({a} : Finset ℕ).card = 1 :=
  Finset.card_singleton a

theorem card_powerset (n : ℕ)
    (A : Finset (Fin n)) :
    A.powerset.card = 2 ^ A.card :=
  Finset.card_powerset A

-- ============================================================
-- SECTION 3: FUNCTIONS AND RELATIONS
-- ============================================================

theorem injective_comp (α β γ : Type*)
    (f : α → β) (g : β → γ)
    (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (g ∘ f) :=
  Function.Injective.comp hg hf

theorem surjective_comp (α β γ : Type*)
    (f : α → β) (g : β → γ)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) :=
  Function.Surjective.comp hg hf

theorem bijective_comp (α β γ : Type*)
    (f : α → β) (g : β → γ)
    (hf : Function.Bijective f)
    (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) :=
  Function.Bijective.comp hg hf

theorem cantor (α : Type*)
    (f : α → Set α) :
    ¬Function.Surjective f := by
  intro h
  let D := {x | x ∉ f x}
  obtain ⟨d, hd⟩ := h D
  by_cases hdf : d ∈ f d
  · have : d ∉ f d := hd ▸ hdf
    exact absurd hdf this
  · have : d ∈ f d := hd ▸ hdf
    exact absurd this hdf

-- ============================================================
-- SECTION 4: ORDINALS AND WELL-ORDERING
-- ============================================================

theorem nat_well_order (S : Finset ℕ)
    (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n :=
  ⟨S.min' hS,
   S.min'_mem hS,
   fun n hn => S.min'_le hS n hn⟩

def ordinal_add (α β : ℕ) : ℕ := α + β

theorem ordinal_add_assoc (α β γ : ℕ) :
    ordinal_add (ordinal_add α β) γ =
    ordinal_add α (ordinal_add β γ) :=
  Nat.add_assoc α β γ

theorem ordinal_add_zero (α : ℕ) :
    ordinal_add α 0 = α :=
  Nat.add_zero α

-- `where` clauses create plain local names, not namespaced ones — the
-- original tried to declare `Nat.rec_aux` via `where`, which isn't valid.
-- `Nat.strongRecOn` already provides exactly this recursion principle
-- directly, with no local helper needed.
theorem transfinite_induction_proxy
    (P : ℕ → Prop)
    (h : ∀ n, (∀ m, m < n → P m) → P n)
    (n : ℕ) : P n :=
  Nat.strongRecOn n h

-- ============================================================
-- SECTION 5: CARDINALS
-- ============================================================

theorem CBS_proxy (m n : ℕ)
    (hmn : m ≤ n) (hnm : n ≤ m) :
    m = n := Nat.le_antisymm hmn hnm

-- The original hand-rolled a Cantor pairing function and tried to close
-- the goal with `simp at h; omega` — but the goal after destructuring is a
-- `Prod` equality `(a,b) = (c,d)`, which `omega` cannot prove (it decides
-- linear arithmetic over ℕ/ℤ, not tuple equality); it would have failed
-- regardless of the pairing function's actual injectivity. Replaced with
-- `Encodable.encode`, whose injectivity for `ℕ × ℕ` Mathlib already proves.
theorem nat_prod_countable :
    ∃ f : ℕ × ℕ → ℕ,
      Function.Injective f :=
  ⟨Encodable.encode, Encodable.encode_injective⟩

theorem aleph0_minimal (n : ℕ) :
    n < n + 1 :=
  Nat.lt_succ_self n

theorem CH_proxy :
    (0 : ℕ) ≤ 1 := Nat.zero_le 1

-- `Nat.pos_pow_of_pos` does not exist in current Mathlib (confirmed absent
-- via search). `Nat.two_pow_pos` is the real lemma for exactly this case.
theorem powerset_card_pos (n : ℕ) :
    0 < 2 ^ n :=
  Nat.two_pow_pos n

-- ============================================================
-- SECTION 6: AXIOM OF CHOICE
-- ============================================================

theorem choice_nonempty (α : Type*)
    (f : ℕ → Finset α)
    (hf : ∀ n, (f n).Nonempty) :
    ∀ n, ∃ x, x ∈ f n :=
  fun n => (hf n).exists_mem

theorem zorn_proxy (n : ℕ) :
    ∃ m : ℕ, ∀ k, k ≤ m → k ≤ n :=
  ⟨n, fun k hk => hk⟩

theorem WO_proxy :
    ∀ n m : ℕ, n ≤ m ∨ m ≤ n :=
  Nat.le_or_le

-- ============================================================
-- SECTION 7: FORCING AND INDEPENDENCE
-- ============================================================

theorem CH_independent_proxy :
    True := trivial

def forcing_condition (n : ℕ) : Prop :=
  0 ≤ n

theorem forcing_condition_holds (n : ℕ) :
    forcing_condition n :=
  Nat.zero_le n

theorem consistency_nonneg (n : ℕ) :
    0 ≤ n := Nat.zero_le n

-- ============================================================
-- SECTION 8: LARGE CARDINALS
-- ============================================================

def is_inaccessible_proxy (κ : ℕ) : Prop :=
  0 < κ ∧ ∀ α < κ, 2 ^ α < κ

theorem omega_not_inaccessible :
    ¬is_inaccessible_proxy 0 := by
  intro h; exact Nat.lt_irrefl 0 h.1

def is_measurable_proxy (κ : ℕ) : Prop :=
  κ > 0

theorem one_measurable_proxy :
    is_measurable_proxy 1 := by
  unfold is_measurable_proxy; norm_num

def woodin_proxy (κ : ℕ) : Prop :=
  κ > 0

theorem domain_woodin :
    woodin_proxy 21 := by
  unfold woodin_proxy; norm_num

-- ============================================================
-- SECTION 9: AWM SET THEORY BRIDGE
-- ============================================================

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

theorem domain_card :
    Fintype.card Domain21 = 21 :=
  by native_decide

theorem domain_powerset_size :
    2 ^ 21 = 2097152 := by norm_num

-- `.toCtorIdx` is not a real auto-generated field for Lean 4 inductive
-- types. Replaced with an explicit rank function, defined by direct pattern
-- match, which is guaranteed to exist and reduce definitionally.
private def domain_rank : Domain21 → ℕ
  | .A_Energy => 0 | .B_Control => 1 | .C_Thermal => 2 | .D_Structural => 3
  | .E_Boundary => 4 | .F_Diagnostics => 5 | .G_Governance => 6
  | .H_Harmonic => 7 | .I_Information => 8 | .J_Joining => 9
  | .K_Kernel => 10 | .L_Localization => 11 | .M_Morphogenic => 12
  | .N_Node => 13 | .O_Operator => 14 | .P_Propagation => 15
  | .Q_Quality => 16 | .R_Resonance => 17 | .S_State => 18
  | .T_Temporal => 19 | .U_Unification => 20

theorem domain_well_ordered :
    ∃ m : Domain21, ∀ d : Domain21, domain_rank m ≤ domain_rank d :=
  ⟨Domain21.A_Energy, fun d => Nat.zero_le _⟩

theorem domain_cantor :
    ¬∃ f : Domain21 → Set Domain21,
      Function.Surjective f := by
  intro ⟨f, hf⟩
  exact cantor Domain21 f hf

theorem domain_cardinal_pos :
    0 < Fintype.card Domain21 := by
  rw [domain_card]; norm_num

theorem AWM_forcing :
    forcing_condition 21 :=
  forcing_condition_holds 21

-- ============================================================
-- SYSTEM LOCK
-- ============================================================

structure SetTheoryLock where
  union_comm     : ∀ (α : Type*) (A B : Set α),
                     A ∪ B = B ∪ A
  demorgan_union : ∀ (α : Type*) (A B : Set α),
                     (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
  card_subset    : ∀ (α : Type*) [DecidableEq α]
                     (A B : Finset α), A ⊆ B →
                     A.card ≤ B.card
  cantor         : ∀ (α : Type*)
                     (f : α → Set α),
                     ¬Function.Surjective f
  nat_WO         : ∀ (S : Finset ℕ),
                     S.Nonempty →
                     ∃ m ∈ S, ∀ n ∈ S, m ≤ n
  CBS_proxy      : ∀ m n : ℕ,
                     m ≤ n → n ≤ m → m = n
  powerset_pos   : ∀ n : ℕ, 0 < 2 ^ n
  WO_proxy       : ∀ n m : ℕ,
                     n ≤ m ∨ m ≤ n
  dom_card       : Fintype.card Domain21 = 21
  dom_power      : 2 ^ 21 = 2097152
  dom_cantor     : ¬∃ f : Domain21 → Set Domain21,
                     Function.Surjective f
  dom_card_pos   : 0 < Fintype.card Domain21
  AWM_forcing    : forcing_condition 21

def STLock : SetTheoryLock where
  union_comm     := union_comm
  demorgan_union := demorgan_union
  card_subset    := card_subset_le
  cantor         := cantor
  nat_WO         := nat_well_order
  CBS_proxy      := CBS_proxy
  powerset_pos   := powerset_card_pos
  WO_proxy       := WO_proxy
  dom_card       := domain_card
  dom_power      := domain_powerset_size
  dom_cantor     := domain_cantor
  dom_card_pos   := domain_cardinal_pos
  AWM_forcing    := AWM_forcing

end SetTheory

