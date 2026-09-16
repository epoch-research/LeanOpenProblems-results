import Submission.Spec
open Nat

def A238224_eval (n : ℕ) : ℕ :=
  Id.run <| do
    let mut sum := 0
    for j in [1:n] do
      let upper_q := (n - 1) / j
      for q in [1:upper_q+1] do
        let k := j * q + 1
        if Nat.primeCounting (k * n) % Nat.primeCounting (j * n) == 0 then
          sum := sum + 1
    return sum

#eval A238224_eval 2
#eval A238224_eval 3
#eval A238224_eval 4
