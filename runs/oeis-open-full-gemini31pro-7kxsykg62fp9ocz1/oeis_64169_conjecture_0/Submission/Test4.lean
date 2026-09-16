import FormalConjectures.Util.ProblemImports
open Rat
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)
#eval A064169 2
