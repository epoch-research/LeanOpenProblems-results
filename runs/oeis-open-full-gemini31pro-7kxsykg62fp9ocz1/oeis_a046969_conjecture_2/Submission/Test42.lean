import Submission.Spec
open Rat Nat

noncomputable def my_a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

#eval my_a 7
#eval (my_a 7) / 12
#eval Nat.Prime ((my_a 7) / 12)
