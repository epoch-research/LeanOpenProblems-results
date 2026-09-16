import Submission.Spec
open Rat Nat

noncomputable def a_comp (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

theorem a_comp_eq_a (n : ℕ) : a_comp n = a n := rfl

#eval a_comp 7
#eval Nat.Prime (a_comp 7 / 12)
