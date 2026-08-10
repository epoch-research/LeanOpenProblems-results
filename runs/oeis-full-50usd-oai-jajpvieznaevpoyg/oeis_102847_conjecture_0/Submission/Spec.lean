import FormalConjectures.Util.ProblemImports


/--
A102847: $a(0)=1$, $a(n) = a(n-1)^2 + 2$.
-/
def a : ℕ → ℕ
| 0     => 1
| n + 1 => (a n) ^ 2 + 2

/--
oeis_102847_conjecture_0: Prime for a(1)=3, a(2)=11, a(4)=15131; semiprime for a(3) = 123 = 3 * 41, a(5) = 228947163 = 3 * 76315721.
a(6), added by Jonathan Vos Post, has 4 prime factors. a(7) = 41 * 811^2 * 106693969 * 317171188688357726699 * 8272236925540996054440172449761.
When is the next prime in the sequence?

Formalization: Does there exist a prime term after a(4)?
-/
theorem oeis_102847_conjecture_0 : ∃ n : ℕ, 4 < n ∧ Nat.Prime (a n) := by
  sorry
