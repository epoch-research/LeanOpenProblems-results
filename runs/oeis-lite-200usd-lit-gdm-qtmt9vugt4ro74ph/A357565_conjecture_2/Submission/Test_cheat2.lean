import FormalConjectures.Util.ProblemImports

open Finset Nat

def MyRel (P : Prop) (x y : Bool) : Prop :=
  (x = true ∧ y = false ∧ P) ∨ (x = false ∧ y = true ∧ P) ∨ (x = y)

inductive MyType3 (P : Prop) : Type where
  | mk : ((Quot.mk (MyRel P) true = Quot.mk (MyRel P) false) → MyType3 P) → MyType3 P
deriving Nonempty

partial def get_mytype3 (P : Prop) : MyType3 P :=
  get_mytype3 P

-- Let's see if we can write a function to extract P.
def f_raw (P : Prop) : Bool → Prop
  | true => True
  | false => P

theorem f_congr (P : Prop) (x y : Bool) (h : MyRel P x y) : f_raw P x = f_raw P y := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | h
  · subst h1 h2
    have : P = True := propext ⟨fun _ => trivial, fun _ => h3⟩
    rw [this]; rfl
  · subst h1 h2
    have : P = True := propext ⟨fun _ => trivial, fun _ => h3⟩
    rw [this]; rfl
  · subst h
    rfl

def f (P : Prop) (q : Quot (MyRel P)) : Prop :=
  Quot.lift (f_raw P) (f_congr P) q

theorem get_P_from_eq (P : Prop) (eq_h : Quot.mk (MyRel P) true = Quot.mk (MyRel P) false) : P := by
  have h1 : f P (Quot.mk (MyRel P) true) := trivial
  rw [eq_h] at h1
  exact h1

-- Can we write a partial function that returns P?
-- Wait, if we use a partial def that returns Decidable P:
partial def get_dec (P : Prop) : Decidable P :=
  get_dec P
