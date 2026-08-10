import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

def B (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

example (n : ℕ) : B n > 0 ↔ n ≠ 19 := by
  native_decide +revert
