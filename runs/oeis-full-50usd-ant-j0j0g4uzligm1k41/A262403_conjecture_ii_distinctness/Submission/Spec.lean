import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- The $x$-th triangular number. -/
def T (x : ℕ) : ℕ := x * (x + 1) / 2

/-- The number of primes not exceeding the $x$-th triangular number. -/
def pi_T (x : ℕ) : ℕ := Nat.primeCounting (T x)

/--
A262403: Number of ways to write $\pi(T(n)) = \pi(T(k)) + \pi(T(m))$ with $1 < k < m < n$,
where $T(x)$ is the triangular number $x(x+1)/2$, and $\pi(x)$ is the number of primes not exceeding x.
-/
def A262403 (n : ℕ) : ℕ :=
  let target_val := pi_T n
  -- The iteration ensures $1 < k$ and $k < m < n$
  (Icc 2 (n - 2)).sum fun k =>
    ((Icc (k + 1) (n - 1)).filter fun m =>
      target_val = pi_T k + pi_T m).card

/--
Conjecture (ii) first assertion: All those numbers pi(T(n)) (n = 1,2,3,...) are pairwise distinct.
This is equivalent to the function x \mapsto pi(T(x))$ being injective.
-/
theorem A262403_conjecture_ii_distinctness.disproof :
  ¬ Function.Injective pi_T := by
  intro h
  -- pi_T 0 = π(T 0) = π(0) = 0 and pi_T 1 = π(T 1) = π(1) = 0, but 0 ≠ 1.
  have : (0 : ℕ) = 1 := h (by decide)
  exact absurd this (by decide)
