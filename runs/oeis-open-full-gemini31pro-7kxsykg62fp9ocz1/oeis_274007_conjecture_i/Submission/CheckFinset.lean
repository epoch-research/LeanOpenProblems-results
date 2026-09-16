import Mathlib

def test : Bool :=
  11 ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)

#eval test
