import FormalConjectures.Util.ProblemImports
open Nat Finset
def A262439 (n : ℕ) : ℕ := primeCounting (n * (n + 1) / 2 + 1)
#eval A262439 10
#eval A262439 100
#eval A262439 1000
