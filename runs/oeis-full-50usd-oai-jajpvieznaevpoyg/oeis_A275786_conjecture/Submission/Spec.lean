import FormalConjectures.Util.ProblemImports

open Nat

/--
The $d$-th triangular number, $T(d) = d(d+1)/2$.
-/
def T_triangular (d : ℕ) : ℕ := d * (d + 1) / 2

/--
A275786: $a(n) = \prod_{d|n} T(d)$ where $T(x)$ is the $x$-th triangular number.
-/
def a (n : ℕ) : ℕ :=
  (Nat.divisors n).prod T_triangular

/-- A275786 Conjecture: the sequence is injective (all terms of this sequence occur only once). -/
theorem oeis_A275786_conjecture :
  ∀ n m : ℕ, n > 0 → m > 0 → (a n = a m → n = m) :=
  by sorry
