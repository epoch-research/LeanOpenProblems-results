import FormalConjectures.Util.ProblemImports

open Rat

def fast_A064169_mod (n : ℕ) : ℕ :=
  -- we only need (num - den) % n
  -- we can compute the harmonic number exactly, but 283 million iterations...
  0

def loop_test (n : ℕ) : ℕ :=
  Id.run do
    let mut s : ℕ := 0
    for i in [1:n] do
      s := s + 1
    return s

#eval loop_test 283686649
