import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A117531: Number of primes in the $n$-th row of the triangle in A117530.
The elements of the $n$-th row of A117530 are $T(n, k) = k^2 - k + p_n$ for $1 \le k \le n$,
where $p_n$ is the $n$-th prime ($p_1=2, p_2=3, \dots$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- The sequence is defined for n >= 1. Icc 1 0 is empty, correctly yielding 0 for n=0.
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  -- We count how many terms T(n, k) are prime for k in {1, 2, ..., n}.
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

/--
Conjecture: $a(n) < n$ for $n > 13$.
-/
theorem oeis_117531_conjecture_0 (n : ℕ) (h : n > 13) : a n < n := by
  sorry
