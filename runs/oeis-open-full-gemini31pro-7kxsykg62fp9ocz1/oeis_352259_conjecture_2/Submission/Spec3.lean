import FormalConjectures.Util.ProblemImports
open Nat Finset

def check_rep (n : ℕ) : Bool :=
  Id.run do
    for w in [0:n+1] do
      if 2 * w^4 > n then continue
      for x in [0:n+1] do
        if 2 * w^4 + 3 * x^2 > n then continue
        for y in [0:n+1] do
          if 2 * w^4 + 3 * x^2 + y^2 > n then continue
          for z in [0:n+1] do
            if 2 * w^4 + 3 * x^2 + y^2 + z^2 + x*y*z == n then return true
    return false

def find_missing : ℕ :=
  Id.run do
    for n in [0:1000] do
      if !check_rep n then return n
    return 9999

#eval find_missing
