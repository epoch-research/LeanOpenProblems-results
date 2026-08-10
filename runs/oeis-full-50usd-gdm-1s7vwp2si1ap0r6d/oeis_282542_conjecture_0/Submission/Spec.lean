import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
A282542: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that $x + 3y + 5z$ is a square and (at least) one of $y,z,w$ are squares.
-/
def A282542 (n : ℕ) : ℕ :=
  (range (Nat.sqrt n + 1)).sum fun x =>
    (range (Nat.sqrt n + 1)).sum fun y =>
      (range (Nat.sqrt n + 1)).sum fun z =>
        (range (Nat.sqrt n + 1)).sum fun w =>
          if x^2 + y^2 + z^2 + w^2 = n ∧
             IsSquare (x + 3 * y + 5 * z) ∧
             (IsSquare y ∨ IsSquare z ∨ IsSquare w)
          then 1 else 0

/--
Conjecture: a(n) > 0 for all n = 0,1,2,....
-/
theorem oeis_282542_conjecture_0 (n : ℕ) : A282542 n > 0 := sorry

