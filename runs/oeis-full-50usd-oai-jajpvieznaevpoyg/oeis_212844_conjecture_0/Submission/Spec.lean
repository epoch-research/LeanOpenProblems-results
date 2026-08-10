import FormalConjectures.Util.ProblemImports
open Function

/--
A212844: $a(n) = 2^{n+2} \bmod n$.
Since the OEIS sequence starts at $n=1$, the Lean function $a(n)$ returns the $(n+1)$-th term of the sequence.
The $(n+1)$-th term is calculated by substituting $n+1$ into $2^{n+2} \bmod n$.
-/
def a : ℕ → ℕ
| 0     => 0
| (n+1) => (2 ^ ((n + 1) + 2)) % (n + 1)

/-- A212844 Conjecture: every integer k >= 0 appears in a(n) at least once. -/
theorem oeis_212844_conjecture_0 : Surjective a := by
  sorry
