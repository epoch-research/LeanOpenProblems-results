import FormalConjectures.Util.ProblemImports

open Nat

/--
A259667: Catalan numbers mod 6.
$$a(n) = C_n \bmod 6$$
where $C_n = \frac{1}{n+1} \binom{2n}{n}$ is the $n$-th Catalan number (A000108).
-/
def A259667 (n : ℕ) : ℕ := ((2 * n).choose n / (n + 1)) % 6

/--
It is conjectured that the only k which yield a(2^k-1) = 1 are k = 0, 1 and 5.
Are there other k than 2 and 8 that yield a(2^k-1) = 5?
Otherwise said, is a(2^k-1) = 3 for all k > 8.
-/
theorem oeis_259667_conjecture_0 :
    (∀ k : ℕ, A259667 (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5) ∧
    (∀ k : ℕ, A259667 (2^k - 1) = 5 ↔ k = 2 ∨ k = 8) ∧
    (∀ k : ℕ, k > 8 → A259667 (2^k - 1) = 3) := by
  sorry
