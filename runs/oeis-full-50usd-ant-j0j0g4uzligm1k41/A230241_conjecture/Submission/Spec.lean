import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A230241: Number of ways to write $n = p + q$ with $p$, $3p - 10$ and $(p-1)q - 1$ all prime, where $q$ is a positive integer.
We count the number of possible values for $p$. Since $p$ must be positive and $q = n-p$ must be positive, we restrict $p$ to the set $\{1, 2, \dots, n-1\}$.
-/
def A230241 (n : ℕ) : ℕ :=
  card $ filter (fun p =>
    Nat.Prime p ∧
    Nat.Prime (3 * p - 10) ∧
    let q := n - p
    Nat.Prime ((p - 1) * q - 1)
  ) (Finset.Icc 1 (n - 1))

/--
Conjecture: a(n) > 0 for all n > 5.
This implies A. Murthy's conjecture mentioned in A109909.
-/
theorem A230241_conjecture (n : ℕ) (hn : n > 5) : A230241 n > 0 := by
  sorry
