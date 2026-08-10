import FormalConjectures.Util.ProblemImports

open Nat

/--
A291624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that $p = x + 2y + 5z$, $p - 2$ and $p + 4$ are all prime.
-/
def A291624 (n : ℕ) : ℕ :=
  let B : ℕ := sqrt n
  Finset.sum (Finset.range (B + 1)) fun x =>
  Finset.sum (Finset.range (B + 1)) fun y =>
  Finset.sum (Finset.range (B + 1)) fun z =>
    let sq_sum_xyz := x^2 + y^2 + z^2
    if sq_sum_xyz ≤ n then
      let r := n - sq_sum_xyz
      let w := sqrt r
      if w^2 = r then
        -- We have found a valid quadruple (x, y, z, w) such that x^2 + y^2 + z^2 + w^2 = n
        let p := x + 2 * y + 5 * z
        -- Check the prime triple condition. Note: p-2 is Nat.sub
        if Nat.Prime p ∧ Nat.Prime (p - 2) ∧ Nat.Prime (p + 4)
        then 1
        else 0
      else 0
    else 0

/-- Conjecture: a(n) > 0 for all n > 1 not divisible by 4. -/
theorem oeis_291624_conjecture_1 (n : ℕ) : n > 1 ∧ ¬ (4 ∣ n) → A291624 n > 0 := sorry



