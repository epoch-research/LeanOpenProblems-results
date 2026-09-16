import FormalConjectures.Util.ProblemImports

open Rat

def A064169_alt (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)

def check (n : ℕ) : Bool :=
  if n <= 2 then true
  else if n.Prime then true
  else (A064169_alt (n - 2)) % n != 0

#eval (List.range 2000).all check
