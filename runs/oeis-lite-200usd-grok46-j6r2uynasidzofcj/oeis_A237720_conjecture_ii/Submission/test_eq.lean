import FormalConjectures.Util.ProblemImports

open Nat

def intervalHasPrimeIter (lo len : ℕ) : Bool :=
  Id.run do
    let mut i := lo
    let mut k := len
    while k > 0 do
      if i.Prime then
        return true
      i := i + 1
      k := k - 1
    return false

#print intervalHasPrimeIter
