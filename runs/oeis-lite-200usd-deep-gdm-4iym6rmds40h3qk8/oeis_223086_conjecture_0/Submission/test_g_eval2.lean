import FormalConjectures.Util.ProblemImports

open Nat

def g (y : ℕ) : ℕ :=
  if y % 3 = 0 then
    2 * y / 3
  else if y % 3 = 1 then
    (4 * y - 1) / 3
  else -- y % 3 = 2
    (4 * y + 1) / 3

def find_drop_65 : ℕ → ℕ → Option ℕ
  | 0, _ => Option.none
  | n + 1, y =>
    let next := g y
    if next < 65 then
      Option.some (n + 1)
    else
      find_drop_65 n next

#eval find_drop_65 10000 (g 64)
