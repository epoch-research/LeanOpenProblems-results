import Submission.Spec
open Nat

def check_A238224 (max_n : ℕ) : IO Unit := do
  for n in [2:max_n] do
    let mut sum := 0
    for j in [1:n] do
      let upper_q := (n - 1) / j
      for q in [1:upper_q+1] do
        let k := j * q + 1
        if Nat.primeCounting (k * n) % Nat.primeCounting (j * n) == 0 then
          sum := sum + 1
    if sum == 0 then
      IO.println s!"COUNTEREXAMPLE IN LEAN: {n}"

#eval check_A238224 500
