import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A303543: Number of ways to write $n$ as $a^2 + b^2 + C(k) + C(m)$ with $0 \le a \le b$ and $0 < k \le m$,
where $C(k)$ denotes the Catalan number $\binom{2k}{k}/(k+1)$.
-/
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
        if C_sum ≤ n then
          count_sum_two_squares_ordered (n - C_sum)
        else
          0
      else
        0

theorem oeis_A303543_conjecture_1 : ∀ (n : ℕ), n > 1 → A303543 n > 0 := by
  sorry

theorem oeis_A303543_conjecture_1.disproof : ¬ (∀ (n : ℕ), n > 1 → A303543 n > 0) := by
  sorry
