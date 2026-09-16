import FormalConjectures.Util.ProblemImports
open Rat
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)

def check_one (n : ℕ) : Bool :=
  if n <= 2 then true
  else
    let d := A064169 (n - 2)
    let p := n.Prime
    (n ∣ d) == p

#eval (List.range 200).all check_one
