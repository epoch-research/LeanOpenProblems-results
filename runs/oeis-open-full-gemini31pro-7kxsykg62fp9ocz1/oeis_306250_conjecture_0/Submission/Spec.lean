import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A306250: Number of ways to write $n$ as $x(3x+1) + y(3y-1) + z(3z+2) + w(3w-2)$,
where $x,y,z,w$ are nonnegative integers with $x \cdot y \cdot z = 0$.
-/
def A306250 (n : ℕ) : ℕ :=
  let T₁ (x : ℕ) : ℕ := x * (3 * x + 1)
  let T₂ (y : ℕ) : ℕ := y * (3 * y - 1)
  let T₃ (z : ℕ) : ℕ := z * (3 * z + 2)
  let T₄ (w : ℕ) : ℕ := w * (3 * w - 2)

  let R := range (n + 1)

  R.sum fun x =>
    R.sum fun y =>
      R.sum fun z =>
        R.sum fun w =>
          if (x = 0 ∨ y = 0 ∨ z = 0) ∧ T₁ x + T₂ y + T₃ z + T₄ w = n then
            1
          else
            0

/--
Conjecture: a(n) > 0 for any nonnegative integer n.
-/
theorem oeis_306250_conjecture_0 (n : ℕ) : A306250 n > 0 := sorry

theorem oeis_306250_conjecture_0.disproof : ¬ (type_of% @oeis_306250_conjecture_0) := sorry
