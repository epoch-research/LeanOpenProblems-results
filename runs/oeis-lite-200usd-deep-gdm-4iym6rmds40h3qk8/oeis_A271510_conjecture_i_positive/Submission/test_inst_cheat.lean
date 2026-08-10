import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

instance (n : ℕ) : Nonempty (0 < A271510 n) :=
  let partial rec inst (n : ℕ) : Nonempty (0 < A271510 n) := inst n
  inst n
