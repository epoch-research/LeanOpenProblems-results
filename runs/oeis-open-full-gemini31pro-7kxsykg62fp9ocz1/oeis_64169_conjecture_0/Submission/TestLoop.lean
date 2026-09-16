import FormalConjectures.Util.ProblemImports

def sum_inv (n : ℕ) (mod : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    for i in [1:n+1] do
      -- compute inverse of i mod `mod`. Wait, ZMod inverse is slow if we use Extended Euclidean.
      -- we can precompute or just use Fermat's Little Theorem? No, mod is n, not prime.
      s := (s + 1) % mod
    return s

#eval sum_inv 283686647 283686649
