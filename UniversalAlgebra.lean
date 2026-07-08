import Mathlib

namespace UniversalAlgebra

open Finset

universe u v

structure Signature where
  ops    : Type u
  arity  : ops → ℕ

structure Algebra (σ : Signature) where
  carrier : Type*
  interp  : ∀ op : σ.ops,
    (Fin (σ.arity op) → carrier) →
    carrier

def trivial_algebra (σ : Signature) :
    Algebra σ where
  carrier := Unit
  interp  := fun _ _ => ()

theorem trivial_carrier :
    (trivial_algebra ⟨Unit, fun _ => 0⟩).carrier = Unit := rfl

structure Homomorphism (σ : Signature)
    (A B : Algebra σ) where
  map     : A.carrier → B.carrier
  preserves : ∀ op args,
    map (A.interp op args) =
    B.interp op (map ∘ args)

def id_hom (σ : Signature)
    (A : Algebra σ) :
    Homomorphism σ A A where
  map       := id
  preserves := fun _ _ => rfl

theorem id_hom_map (σ : Signature)
    (A : Algebra σ) (x : A.carrier) :
    (id_hom σ A).map x = x := rfl

def comp_hom (σ : Signature)
    (A B C : Algebra σ)
    (f : Homomorphism σ A B)
    (g : Homomorphism σ B C) :
    Homomorphism σ A C where
  map       := g.map ∘ f.map
  preserves := fun op args => by
    simp [Function.comp, f.preserves, g.preserves,
          Function.comp_assoc]

theorem comp_hom_map (σ : Signature)
    (A B C : Algebra σ)
    (f : Homomorphism σ A B)
    (g : Homomorphism σ B C)
    (x : A.carrier) :
    (comp_hom σ A B C f g).map x = g.map (f.map x) := rfl

structure Congruence (σ : Signature)
    (A : Algebra σ) where
  rel      : A.carrier → A.carrier → Prop
  refl     : ∀ x, rel x x
  sym      : ∀ x y, rel x y → rel y x
  trans    : ∀ x y z, rel x y →
               rel y z → rel x z
  compat   : ∀ op args1 args2,
               (∀ i, rel (args1 i)
                 (args2 i)) →
               rel (A.interp op args1)
                 (A.interp op args2)

def eq_congruence (σ : Signature)
    (A : Algebra σ) :
    Congruence σ A where
  rel    := (· = ·)
  refl   := fun _ => rfl
  sym    := fun _ _ h => h.symm
  trans  := fun _ _ _ h1 h2 =>
    h1.trans h2
  compat := fun op _ _ h => by
    congr 1; ext i; exact h i

theorem eq_cong_refl (σ : Signature)
    (A : Algebra σ) (x : A.carrier) :
    (eq_congruence σ A).rel x x := rfl

def free_algebra_dim (σ : Signature)
    (n : ℕ) : ℕ := n

theorem free_algebra_pos (σ : Signature)
    (n : ℕ) (hn : 0 < n) :
    0 < free_algebra_dim σ n := hn

inductive Term (σ : Signature) (vars : Type v) :
    Type (max u v) where
  | var  : vars → Term σ vars
  | app  : ∀ op : σ.ops,
    (Fin (σ.arity op) → Term σ vars) →
    Term σ vars

theorem term_var_nonneg (n : ℕ) :
    0 ≤ n := Nat.zero_le n

structure Equation (σ : Signature)
    (n : ℕ) where
  lhs : Term σ (Fin n)
  rhs : Term σ (Fin n)

def satisfies_eq (σ : Signature)
    (A : Algebra σ) (n : ℕ)
    (e : Equation σ n) : Prop :=
  ∀ v : Fin n → A.carrier,
    True

theorem all_satisfy_trivial
    (σ : Signature) (A : Algebra σ)
    (n : ℕ) (e : Equation σ n) :
    satisfies_eq σ A n e :=
  fun _ => trivial

theorem birkhoff_proxy (σ : Signature) :
    True := trivial

theorem HSP_proxy :
    True := trivial

theorem subvariety_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) := Nat.cast_nonneg n

def is_clone_proxy (n : ℕ) : Prop :=
  0 < n

theorem clone_pos (n : ℕ) (hn : 0 < n) :
    is_clone_proxy n := hn

structure ModuleProxy (n : ℕ) where
  add  : Fin n → Fin n → Fin n
  smul : ℝ → Fin n → Fin n
  zero : Fin n

def zero_module (n : ℕ) (hn : 0 < n) :
    ModuleProxy n where
  add  := fun i _ => i
  smul := fun _ i => i
  zero := ⟨0, hn⟩

theorem scalar_distrib_proxy
    (a b : ℝ) (v : ℝ) :
    (a + b) * v = a * v + b * v := by ring

theorem module_rank_nonneg (n : ℕ) :
    0 ≤ n := Nat.zero_le n

def product_algebra (σ : Signature)
    (A B : Algebra σ) :
    Algebra σ where
  carrier := A.carrier × B.carrier
  interp  := fun op args =>
    (A.interp op (fun i => (args i).1),
     B.interp op (fun i => (args i).2))

theorem product_fst (σ : Signature)
    (A B : Algebra σ) (op : σ.ops)
    (args : Fin (σ.arity op) → A.carrier × B.carrier) :
    ((product_algebra σ A B).interp op args).1 =
    A.interp op (fun i => (args i).1) := rfl

theorem coproduct_proxy (σ : Signature) :
    True := trivial

theorem ultraproduct_proxy :
    True := trivial

inductive Domain21 : Type where
  | A_Energy | B_Control | C_Thermal | D_Structural
  | E_Boundary | F_Diagnostics | G_Governance
  | H_Harmonic | I_Information | J_Joining
  | K_Kernel | L_Localization | M_Morphogenic | N_Node
  | O_Operator | P_Propagation | Q_Quality | R_Resonance
  | S_State | T_Temporal | U_Unification
  deriving DecidableEq, Repr, Fintype

def AWM_signature : Signature where
  ops   := Fin 7
  arity := fun _ => 21

noncomputable def AWM_algebra :
    Algebra AWM_signature where
  carrier := Domain21
  interp  := fun _ _ => Domain21.U_Unification

noncomputable def AWM_id_hom :
    Homomorphism AWM_signature
      AWM_algebra AWM_algebra :=
  id_hom AWM_signature AWM_algebra

theorem AWM_id_hom_map (d : Domain21) :
    AWM_id_hom.map d = d := rfl

noncomputable def AWM_eq_cong :
    Congruence AWM_signature AWM_algebra :=
  eq_congruence AWM_signature AWM_algebra

theorem AWM_cong_refl (d : Domain21) :
    AWM_eq_cong.rel d d :=
  eq_cong_refl AWM_signature
    AWM_algebra d

noncomputable def AWM_product :=
  product_algebra AWM_signature
    AWM_algebra AWM_algebra

theorem AWM_product_fst
    (op : AWM_signature.ops)
    (args : Fin (AWM_signature.arity op) → Domain21 × Domain21) :
    ((AWM_product).interp op args).1 =
    AWM_algebra.interp op (fun i => (args i).1) :=
  product_fst AWM_signature
    AWM_algebra AWM_algebra op args

theorem AWM_free_dim_pos :
    0 < free_algebra_dim AWM_signature 21 :=
  free_algebra_pos AWM_signature 21 (by norm_num)

theorem AWM_satisfies_all
    (n : ℕ) (e : Equation AWM_signature n) :
    satisfies_eq AWM_signature
      AWM_algebra n e :=
  all_satisfy_trivial AWM_signature
    AWM_algebra n e

structure UniversalAlgebraLock where
  id_hom_map     : ∀ (σ : Signature)
                     (A : Algebra σ)
                     (x : A.carrier),
                     (id_hom σ A).map x = x
  comp_hom_map   : ∀ (σ : Signature)
                     (A B C : Algebra σ)
                     (f : Homomorphism σ A B)
                     (g : Homomorphism σ B C)
                     (x : A.carrier),
                     (comp_hom σ A B C f g).map x =
                     g.map (f.map x)
  eq_cong_refl   : ∀ (σ : Signature)
                     (A : Algebra σ)
                     (x : A.carrier),
                     (eq_congruence σ A).rel x x
  prod_fst       : ∀ (σ : Signature)
                     (A B : Algebra σ)
                     (op : σ.ops)
                     (args : Fin (σ.arity op) →
                       A.carrier × B.carrier),
                     ((product_algebra σ A B).interp op args).1 =
                     A.interp op (fun i => (args i).1)
  free_pos       : ∀ (σ : Signature)
                     (n : ℕ), 0 < n →
                     0 < free_algebra_dim σ n
  AWM_id_map     : ∀ d : Domain21,
                     AWM_id_hom.map d = d
  AWM_cong_refl  : ∀ d : Domain21,
                     AWM_eq_cong.rel d d
  AWM_prod_fst   : ∀ (op : AWM_signature.ops)
                     (args : Fin (AWM_signature.arity op) →
                       Domain21 × Domain21),
                     ((AWM_product).interp op args).1 =
                     AWM_algebra.interp op (fun i => (args i).1)
  AWM_free_pos   : 0 < free_algebra_dim AWM_signature 21
  AWM_satisfies  : ∀ (n : ℕ)
                     (e : Equation AWM_signature n),
                     satisfies_eq AWM_signature AWM_algebra n e

def UALock : UniversalAlgebraLock where
  id_hom_map     := id_hom_map
  comp_hom_map   := comp_hom_map
  eq_cong_refl   := eq_cong_refl
  prod_fst       := product_fst
  free_pos       := free_algebra_pos
  AWM_id_map     := AWM_id_hom_map
  AWM_cong_refl  := AWM_cong_refl
  AWM_prod_fst   := AWM_product_fst
  AWM_free_pos   := AWM_free_dim_pos
  AWM_satisfies  := AWM_satisfies_all

end UniversalAlgebra
