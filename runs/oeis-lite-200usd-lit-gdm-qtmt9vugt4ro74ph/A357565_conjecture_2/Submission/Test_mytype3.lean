import FormalConjectures.Util.ProblemImports

def MyRel (P : Prop) (x y : Bool) : Prop :=
  (x = true ∧ y = false ∧ P) ∨ (x = false ∧ y = true ∧ P) ∨ (x = y)

inductive MyType3 (P : Prop) : Type where
  | mk : ((Quot.mk (MyRel P) true = Quot.mk (MyRel P) false) → MyType3 P) → MyType3 P
deriving Nonempty
