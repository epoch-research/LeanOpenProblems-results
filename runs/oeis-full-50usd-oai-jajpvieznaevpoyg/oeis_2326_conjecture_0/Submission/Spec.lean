import FormalConjectures.Util.ProblemImports

open Nat

/--
A002326: Multiplicative order of 2 mod 2n+1.
In other words, least $m > 0$ such that $2n+1$ divides $2^m-1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  orderOf (2 : ZMod (2 * n + 1))

/--
Conjecture: if $p$ is an odd prime then $a((p^3-1)/2) = p \cdot a((p^2-1)/2)$.
Because otherwise $a((p^3-1)/2) < p \cdot a((p^2-1)/2)$ iff $a((p^3-1)/2) = a((p-1)/2)$ for a prime $p$.
Equivalently $p^3$ divides $2^{p-1}-1$, but no such prime $p$ is known. - Thomas Ordowski, Feb 10 2014
-/
theorem oeis_2326_conjecture_0 (p : ℕ) (hp_prime : p.Prime) (hp_odd : p ≠ 2) :
  a ((p^3 - 1) / 2) = p * a ((p^2 - 1) / 2) := by
  sorry
