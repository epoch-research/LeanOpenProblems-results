import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false

open Nat Lean Elab Command Term

/--
A299068: Number of pairs of factors of $n^2(n^2-1)$ which differ by $n$.
Formally, this is the number of divisors $d$ of $n^2(n^2-1)$ such that $d+n$ is also a divisor of $n^2(n^2-1)$.
-/
def A299068 (n : ℕ) : ℕ :=
  let m : ℕ := n ^ 2 * (n ^ 2 - 1)
  (m.divisors.filter (fun d => d + n ∈ m.divisors)).card



/--
oeis_299068_conjecture_0: If k in A299159 is sufficiently large, then a(12*k-2)=7.
Dickson's conjecture implies there are infinitely many such k, and thus infinitely many n with a(n)=7.
-/
theorem oeis_299068_conjecture_0 : Set.Infinite {n : ℕ | A299068 n = 7} := by
  sorry




