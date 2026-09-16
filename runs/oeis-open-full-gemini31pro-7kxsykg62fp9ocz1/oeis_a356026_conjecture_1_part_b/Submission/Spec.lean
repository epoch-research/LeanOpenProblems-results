import FormalConjectures.Util.ProblemImports
open Nat

def KL_array : ℕ → ℕ → ℕ
| 0, _ => 0
| _, 0 => 0
| i, j =>
  if j ≥ 2 * i - 3 then
    i + j - 1
  else
    let i' := i - 1
    if j % 2 = 0 then
      let next_j := i + (j - 2) / 2
      KL_array i' next_j
    else
      let term := (j + 3) / 2
      let next_j := i - term
      KL_array i' next_j
termination_by i j => i

def a (n : ℕ) : ℕ := KL_array n n

theorem oeis_a356026_conjecture_1_part_b : ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ a n = k :=
by
  sorry

theorem oeis_a356026_conjecture_1_part_b.disproof : ¬ (type_of% @oeis_a356026_conjecture_1_part_b) :=
by sorry
