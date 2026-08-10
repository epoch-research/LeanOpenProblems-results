import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/--
A238902: $a(n) = |\{0 < k \le n: \pi(\pi(k \cdot n)) \text{ is a square}\}|$,
where $\pi(x)$ denotes the number of primes not exceeding $x$.
-/
def a (n : ℕ) : ℕ :=
  Finset.card $ (Finset.Icc 1 n).filter fun k : ℕ =>
    let m := π (π (k * n))
    m.sqrt ^ 2 = m

/--
Conjecture (i): a(n) > 0 for all n > 0.
-/
theorem oeis_a238902_conjecture_i (n : ℕ) (hn : n > 0) : a n > 0 := by
  sorry
