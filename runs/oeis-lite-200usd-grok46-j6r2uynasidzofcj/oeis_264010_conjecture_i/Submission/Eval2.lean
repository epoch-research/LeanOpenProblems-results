import FormalConjectures.Util.ProblemImports

open Nat Finset

def primeCond (k : ℕ) : Bool := k.Prime || (k + 1).Prime

def A_fast (n : ℕ) : ℕ :=
  Id.run do
    let mut cnt := 0
    let xmax := n.sqrt
    let ymax := n.sqrt + 1
    let zmax := (2 * n).sqrt + 1
    for x in [0:xmax+1] do
      for y in [0:ymax+1] do
        if primeCond y then
          for z in [0:zmax+1] do
            if primeCond z then
              if x * x + y * (y + 1) + z * (z + 1) / 2 = n then
                cnt := cnt + 1
    return cnt

#eval [3,4,5,6,7,8,9,10,11,12,13,14,15,20,29,50].map A_fast
#eval A_fast 1125
