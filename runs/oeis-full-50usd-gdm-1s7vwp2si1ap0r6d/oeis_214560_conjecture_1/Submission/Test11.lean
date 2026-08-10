import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  if n = 0 then
    1
  else
    (Nat.digits 2 (n ^ 2)).count 0

def MyConj : Prop := answer(sorry)

theorem oeis_214560_conjecture_1 : MyConj :=
  trivial

#print axioms oeis_214560_conjecture_1
