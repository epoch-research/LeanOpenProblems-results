import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
The $k$-th pentagonal number $P_k = k(3k-1)/2$.
-/
def pentagonal (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/--
A303401: Number of ways to write $n$ as a*(3*a-1)/2 + b*(3*b-1)/2 + 3^c + 3^d with a,b,c,d nonnegative integers.
The counting implicitly assumes $a \le b$ and $c \le d$ to match the sequence data.
Note: The given Lean definition is a direct translation of the counting process,
but the bounds for `a`, `b`, `c`, `d` are loose (`n+1`). Since we are only
formalizing the conjecture, this definition is assumed to be correct.
-/
def A303401 (n : ℕ) : ℕ :=
  let P := pentagonal
  -- A loose but safe upper bound for all indices, since all terms grow at least quadratically or exponentially.
  let max_val : ℕ := n + 1

  -- Outer summation over c and d.
  (range max_val).sum fun c =>
    (range max_val).sum fun d =>
      if c ≤ d ∧ 3^c + 3^d ≤ n then
        let n_prime := n - (3^c + 3^d)

        -- Inner summation over a and b.
        (range max_val).sum fun a =>
          (range max_val).sum fun b =>
            if a ≤ b ∧ P a + P b = n_prime then 1 else 0
      else
        0

/--
Conjecture: a(n) > 0 for all n > 1. In other words, any integer n > 1 can be written as the sum of two pentagonal numbers and two powers of 3.
-/
theorem oeis_303401_conjecture_1 : ∀ (n : ℕ), 1 < n → A303401 n > 0 := by
  sorry
