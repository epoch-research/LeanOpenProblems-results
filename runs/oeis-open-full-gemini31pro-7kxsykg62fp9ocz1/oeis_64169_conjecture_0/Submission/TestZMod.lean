import FormalConjectures.Util.ProblemImports
import Mathlib.Data.ZMod.Basic

def sum_inv (n : ℕ) (p2 : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    for i in [1:n+1] do
      if i % 16843 != 0 then
        -- we need inverse of i mod p2
        -- actually, just sum something simple to see speed
        s := (s + i) % p2
    return s

#eval sum_inv 283686647 283686649
