import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A236511: $a(n) = |\{0 < k < n: p = 3\phi(k) + \phi(n-k) - 1, p + 2, p + 6 \text{ and } p + 8 \text{ are all prime}\}|$, where $\phi(\cdot)$ is Euler's totient function.
-/
def a (n : ℕ) : ℕ :=
  (Ioo 0 n).sum (fun k ↦
    let T := 3 * totient k + totient (n - k)
    -- p = T - 1. The four primes are p, p+2, p+6, p+8, which correspond to T-1, T+1, T+5, T+7.
    if (T - 1).Prime ∧ (T + 1).Prime ∧ (T + 5).Prime ∧ (T + 7).Prime then 1 else 0
  )

/-- Conjecture: a(n) > 0 for all n > 1075. -/
theorem oeis_236511_conjecture_0 : ∀ n : ℕ, n > 1075 → a n > 0 := by sorry
