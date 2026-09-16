import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 2 =>
  let an_1 := a (n + 1)
  let an_2 := a n
  if Nat.Prime an_1 ∧ an_1 > 2 then
    an_1 - an_2
  else
    an_1 + an_2

theorem test4 : a 4 = 3 := by rfl
