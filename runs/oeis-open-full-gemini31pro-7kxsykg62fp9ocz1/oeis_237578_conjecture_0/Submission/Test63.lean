import Mathlib
import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter fun k : ℕ => Nat.Prime (Nat.primeCounting (k * n))).card

#eval (List.range 20).map a
