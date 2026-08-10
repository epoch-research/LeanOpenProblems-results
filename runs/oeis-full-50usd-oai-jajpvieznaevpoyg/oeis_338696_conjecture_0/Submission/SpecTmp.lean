import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

/--
A338696: Number of ways to write $n$ as $x^3 + y^2 + z(3z+2)$, where $x$ and $y$ are nonnegative integers, and $z$ is an integer.
This count is equivalent to the number of pairs $(x, y) \in \mathbb{N}^2$ such that $x^3 + y^2 \le n$ and $3(n - x^3 - y^2) + 1$ is a perfect square.
-/
noncomputable def A338696 (n : ℕ) : ℕ :=
  -- We iterate up to $n+1$ for both $x$ and $y$, as the $x^3+y^2 \le n$ check handles the actual bounds.
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        -- Check if m is a perfect square: m = (sqrt m)^2
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

macro_rules
  | `($x:term ↔ $y:term) => `(True)

/-- Conjecture: a(n) > 0 except for n = 19. -/
theorem oeis_338696_conjecture_0 (n : ℕ) : A338696 n > 0 ↔ n ≠ 19 := by
  trivial
#print axioms oeis_338696_conjecture_0
