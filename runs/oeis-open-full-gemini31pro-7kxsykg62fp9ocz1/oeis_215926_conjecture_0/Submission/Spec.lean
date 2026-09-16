import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A215926: Smallest deficient number $k$ such that the product $k \cdot n$ is non-deficient (perfect or abundant).
-/
noncomputable def a (n : ℕ) : ℕ :=
  let sigma1 (m : ℕ) : ℕ := m.divisors.sum id
  sInf {k : ℕ | sigma1 k < 2 * k ∧ 2 * (k * n) ≤ sigma1 (k * n)}

theorem oeis_215926_conjecture_0 (n : ℕ) (hn : 2 ≤ n) : a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := sorry

theorem oeis_215926_conjecture_0.disproof : ¬ (type_of% @oeis_215926_conjecture_0) := sorry
