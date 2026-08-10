import FormalConjectures.Util.ProblemImports

open Finset Nat

partial def testfoo (n : ℕ) :
  ∃ w x y z : ℕ, n = 4 * w^2 + x * (4 * x + 1) + y * (4 * y - 2) + z * (4 * z - 3) :=
  testfoo n

#print axioms testfoo
#print opaques testfoo
