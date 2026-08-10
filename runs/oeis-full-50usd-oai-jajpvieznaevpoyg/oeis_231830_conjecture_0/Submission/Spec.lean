import FormalConjectures.Util.ProblemImports

/--
A231830: $a(0) = 1$; for $n > 0$, $a(n) = 1 + 4 \cdot \prod_{i=1}^{n-1} a(i)^2$.
The recurrence relation for $n > 1$ is $a(n) = (a(n-1) - 1) \cdot a(n-1)^2 + 1$.
-/
def a : ℕ → ℕ
| 0 => 1
| 1 => 5
| n + 2 => (a (n + 1) - 1) * (a (n + 1))^2 + 1

/--
OEIS A231830 conjecture: Similarly to Sylvester's sequence (A000058), it is unknown if all terms are squarefree.
-/
theorem oeis_231830_conjecture_0 : ∀ n : ℕ, Squarefree (a n) := by
  sorry
