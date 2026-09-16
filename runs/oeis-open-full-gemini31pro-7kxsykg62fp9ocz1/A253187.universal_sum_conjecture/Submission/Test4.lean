import Submission.Spec
open Nat Finset

def checkSecond (k m : ℕ) : IO Unit := do
  for n in [0:100] do
    let mut found := false
    for x in [0:n+1] do
      for y in [0:n+1] do
        for z in [-n : n+1] do
          let sum := P_k_first k x + P_k_second k y + (polygonal_num_val m (z : ℤ)).toNat
          if sum == n then
            found := true
    if not found then
      IO.println s!"Failed for {k}, {m} at {n}"
  IO.println s!"Done for {k}, {m}"

def checkAllSecond : IO Unit := do
  checkSecond 5 7
  checkSecond 5 9
  checkSecond 5 13
  checkSecond 6 5
  checkSecond 6 7
  checkSecond 7 5

#eval checkAllSecond
