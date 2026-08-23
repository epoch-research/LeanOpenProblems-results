import FormalConjectures.Util.ProblemImports

open Nat

def holdsDec (n : ℕ) : Bool :=
  decide (∃ p ∈ Finset.range n, p.Prime ∧ (Nat.sqrt (n + p)).Prime)

-- Test small
#eval holdsDec 3
#eval holdsDec 62
#eval holdsDec 100

-- Check all from 3 to 200
def allHold (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => n ≤ 2 || holdsDec n

#eval allHold 200
