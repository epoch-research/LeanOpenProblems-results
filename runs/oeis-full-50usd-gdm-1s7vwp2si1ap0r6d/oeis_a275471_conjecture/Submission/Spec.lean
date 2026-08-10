import FormalConjectures.Util.ProblemImports

open Nat

/--
A275471: Number of ordered ways to write $n$ as $4^k(1+x^2+y^2)+z^2$, where $k,x,y,z$ are nonnegative integers with $x \le y$ and $x \equiv y \pmod 2$.
-/
def a (n : ℕ) : ℕ :=
  -- We count the number of solutions $(k, x, y, z)$ by summing over finite ranges of $k, x, y$,
  -- and checking if the remainder is a perfect square $z^2$.
  -- Bound for $k$ is loosely $n$. Bound for $x, y$ is $\lfloor\sqrt{n}\rfloor$.
  (Finset.range (n + 1)).sum fun k =>
    (Finset.range (n.sqrt + 1)).sum fun x =>
      (Finset.range (n.sqrt + 1)).sum fun y =>

        let term_inner := 1 + x^2 + y^2
        let term_outer := 4^k * term_inner

        -- 1. Constraints $x \le y$ and $x \equiv y \pmod 2$.
        -- 2. Constraint $4^k(1+x^2+y^2) \le n$ to ensure non-negative remainder $R$.
        if x ≤ y ∧ x % 2 = y % 2 ∧ term_outer ≤ n then
          let R : ℕ := n - term_outer
          -- 3. Constraint $R = z^2$, checked by $z^2 = R$ where $z = \lfloor\sqrt{R}\rfloor$.
          if R.sqrt * R.sqrt = R then 1 else 0
        else 0

set_option allowUnsafeReducibility true
set_option maxRecDepth 10000000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 1000

attribute [local reducible] Nat.sqrt.iter

/-- Conjecture: a(n) > 0 except for n = 449. -/
theorem oeis_a275471_conjecture : ∀ n : ℕ, n > 0 → (a n > 0 ↔ n ≠ 449) := by
  intro n hn
  constructor
  · intro ha hn449
    subst hn449
    have h_zero : a 449 = 0 := by decide
    rw [h_zero] at ha
    contradiction
  · intro hn449
    sorry


