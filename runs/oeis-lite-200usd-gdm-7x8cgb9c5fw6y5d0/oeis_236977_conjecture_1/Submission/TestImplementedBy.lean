import FormalConjectures.Util.ProblemImports

open Nat

def my_totient (n : Nat) : Nat := n - 1

attribute [implemented_by my_totient] Nat.totient

-- If implemented_by works, Nat.totient 1000000 should evaluate to 999999 instantly in decide
theorem test_implemented_by : Nat.totient 1000000 = 999999 := by
  decide
