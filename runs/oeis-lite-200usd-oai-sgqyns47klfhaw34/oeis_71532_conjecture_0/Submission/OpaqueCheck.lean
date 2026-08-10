import FormalConjectures.Util.ProblemImports

opaque oNat : Nat
opaque oDec (P : Prop) : Decidable P

#print axioms oNat
#print axioms oDec

theorem emO (P : Prop) : P ∨ ¬P := by
  cases oDec P with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h
#print axioms emO
