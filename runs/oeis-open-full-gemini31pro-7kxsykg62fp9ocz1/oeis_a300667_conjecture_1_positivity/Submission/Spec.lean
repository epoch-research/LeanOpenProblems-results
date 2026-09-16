import FormalConjectures.Util.ProblemImports

open Nat

/--
A helper function for counting the number of ways to write $k$ as $z^2 + w^2$ with $z, w \ge 0$ and $z \le w$.
-/
def count_restricted_two_squares (k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 = k ∧ p.1 ≤ p.2)
    (Finset.product (Finset.range (sqrt k + 1)) (Finset.range (sqrt k + 1)))
  )

/--
A300667: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$
such that $3*x$ or $y$ is a square and $x + 2*y$ is also a square.
-/
def a (n : ℕ) : ℕ :=
  let is_sq (m : ℕ) : Prop := (sqrt m) * (sqrt m) = m

  Finset.sum (Finset.range (sqrt n + 1)) fun x =>
    let n_minus_x2 := n - x^2
    Finset.sum (Finset.range (sqrt n_minus_x2 + 1)) fun y =>
      if h : is_sq (x + 2 * y) ∧ (is_sq (3 * x) ∨ is_sq y) then
        let k := n_minus_x2 - y^2
        count_restricted_two_squares k
      else 0

theorem oeis_a300667_conjecture_1_positivity (n : ℕ) : a n > 0 := by
  sorry

theorem oeis_a300667_conjecture_1_positivity.disproof : ¬ (type_of% @oeis_a300667_conjecture_1_positivity) := by
  sorry
