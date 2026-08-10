import FormalConjectures.Util.ProblemImports

partial def loopNat : Nat := loopNat
partial def loopDec (P : Prop) : Decidable P := loopDec P

def useNat : Nat := loopNat

theorem decEm (P : Prop) : P ∨ ¬ P := by
  cases loopDec P with
  | isTrue h => exact Or.inl h
  | isFalse h => exact Or.inr h

#print axioms loopNat
#print axioms loopDec
#print axioms useNat
#print axioms decEm
#print loopNat
#print loopDec
