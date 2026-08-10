import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset
noncomputable def A338696 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0
example (n : ℕ) (hn : n ≠ 19) (h : 2000 ≤ n) : A338696 n > 0 := by
  unfold A338696
  grind
