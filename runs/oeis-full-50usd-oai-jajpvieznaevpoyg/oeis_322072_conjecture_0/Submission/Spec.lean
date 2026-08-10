import FormalConjectures.Util.ProblemImports

open BigOperators

/--
The sequence A322072: Row sums of the triangle A322071.
$$a(n) = \sum_{k=1}^n \left\lfloor \frac{2n^k}{k^k} \right\rfloor$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.Icc 1 n) fun k : ℕ =>
    let num : ℕ := 2 * n ^ k
    let den : ℕ := k ^ k
    let term_q : ℚ := (num : ℚ) / (den : ℚ)
    (Rat.floor term_q).toNat

/--
OEIS A322072 Conjecture: The difference $a(n + 1) - a(n)$ between two consecutive terms is not a perfect square except for $n = 1, 5$ and $6$.
-/
theorem oeis_322072_conjecture_0 {n : ℕ} (hn : 1 ≤ n) :
  (∃ m : ℕ, a (n + 1) - a n = m ^ 2) ↔ n = 1 ∨ n = 5 ∨ n = 6 :=
by sorry
