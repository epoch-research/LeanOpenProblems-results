import FormalConjectures.Util.ProblemImports
open Nat Finset
def A303543 (n : ℕ) : ℕ :=
  let count_sum_two_squares_ordered (R : ℕ) : ℕ :=
    let max_a := R / 2 |> Nat.sqrt
    (range (max_a + 1)).sum fun a =>
      let rem := R - a^2
      let b := rem.sqrt
      if b^2 = rem then 1 else 0
  let B := n + 1
  (range B).sum fun k =>
    (range B).sum fun m =>
      if 1 ≤ k ∧ k ≤ m then
        let C_sum := catalan k + catalan m
        if C_sum ≤ n then count_sum_two_squares_ordered (n - C_sum) else 0
      else 0
#eval (List.range 31).map (fun n => A303543 n)
