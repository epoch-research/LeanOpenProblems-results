import Submission.Spec
open Nat

def b := 38
def maxL := 137

partial def dfs (k : ℕ) (delta : ℤ) (Pk : ℕ) : ℕ :=
  if k == maxL then 1
  else
    let bk := b ^ k
    if k > 0 && delta >= 0 && bk >= Pk * (b - 1) then 1
    else
      -- min_future bound
      let rec loop (d : ℕ) (acc : ℕ) : ℕ :=
        if d == b then acc
        else if k == 0 && d == 0 then loop (d + 1) acc
        else
          let n_delta := delta + (d * bk : ℤ) - ((d * d * Pk) : ℤ)
          let n_Pk := Pk * d
          loop (d + 1) (acc + dfs (k + 1) n_delta n_Pk)
      loop 0 0

-- Just test if we can run it
-- actually min_future is hard to compute exactly without loop.
