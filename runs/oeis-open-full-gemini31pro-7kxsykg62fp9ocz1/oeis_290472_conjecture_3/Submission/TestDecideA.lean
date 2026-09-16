import Mathlib
def test_prod : Nat :=
  let X := Finset.range 10
  (X.product X).card
#print axioms test_prod
