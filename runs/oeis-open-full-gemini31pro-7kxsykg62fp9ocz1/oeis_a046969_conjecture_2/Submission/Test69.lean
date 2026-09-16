import FormalConjectures.Util.ProblemImports
open Rat Nat

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

theorem a_7 : a 7 = 156 := by
  unfold a
  norm_num
