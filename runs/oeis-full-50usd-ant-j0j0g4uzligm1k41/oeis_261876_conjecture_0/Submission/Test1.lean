import FormalConjectures.Util.ProblemImports
open Nat Finset BigOperators

def a (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := IsSquare k
  (Finset.range (n + 1)).sum fun x =>
  (Finset.range (n + 1)).sum fun y =>
  (Finset.range (n + 1)).sum fun z =>
    if h_z : z > 0 then
      let k := x^2 + y^2 + z^2
      if h_le : k ≤ n then
        let r := n - k
        if is_square r then
          let condition_expr := (5 * x^2 + 7 * y^2 + 9 * z^2) * y * z
          if is_square condition_expr then 1 else 0
        else 0
      else 0
    else 0

set_option maxRecDepth 10000 in
example : a 7 = 1 := by decide
