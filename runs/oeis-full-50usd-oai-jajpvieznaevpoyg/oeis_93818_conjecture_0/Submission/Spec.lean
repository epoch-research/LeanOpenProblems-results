import FormalConjectures.Util.ProblemImports

open Nat Rat Int

/--
A093818: $a(n) = \gcd(\mathrm{A001008}(n), n!)$.
$\mathrm{A001008}(n)$ is the numerator of the $n$-th harmonic number $H_n = \sum_{i=1}^n \frac{1}{i}$.
-/
def a (n : ℕ) : ℕ :=
  Nat.gcd ((harmonic n).num.natAbs) (n.factorial)

/-- Conjecture: every odd prime occurs as a term in the sequence. -/
theorem oeis_93818_conjecture_0 :
  ∀ (p : ℕ), Nat.Prime p → p ≠ 2 → ∃ (n : ℕ), 0 < n ∧ a n = p :=
by
  intro p hp hp2
  sorry
