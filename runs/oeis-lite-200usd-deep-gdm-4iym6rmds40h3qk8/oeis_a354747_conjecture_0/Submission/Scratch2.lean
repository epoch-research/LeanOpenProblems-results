import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A354747: Start with $2n-1$; repeatedly triple and add 2 until reaching a prime.
$a(n)$ = number of steps until reaching a prime $> 2n-1$, or 0 if no prime is ever reached.
Equivalently, $a(n)$ is the smallest $m \ge 1$ such that $2 \cdot n \cdot 3^m - 1$ is prime.
-/
noncomputable def a354747 (n : ℕ) : ℕ :=
  let prime_steps : Set ℕ :=
    { m : ℕ | m > 0 ∧ Nat.Prime (2 * n * 3 ^ m - 1) }
  sInf prime_steps

theorem oeis_a354747_conjecture_0 : a354747 100943 = 0 := answer(sorry)

#print axioms oeis_a354747_conjecture_0



