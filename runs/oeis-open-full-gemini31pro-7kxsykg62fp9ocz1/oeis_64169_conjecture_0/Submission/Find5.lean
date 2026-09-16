import FormalConjectures.Util.ProblemImports
import Mathlib.Data.Nat.Prime.Basic
open Rat

def A064169_alt (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)

def check_one (n : ℕ) : Bool :=
  if n <= 2 then true
  else
    let div := (A064169_alt (n - 2)) % n == 0
    let pr := n.Prime
    div == pr

#eval! (List.range 1000).all check_one
