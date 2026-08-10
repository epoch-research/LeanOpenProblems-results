import FormalConjectures.Util.ProblemImports
open Rat Nat

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

lemma a_ten_decide : a 10 = 125400 := by decide
