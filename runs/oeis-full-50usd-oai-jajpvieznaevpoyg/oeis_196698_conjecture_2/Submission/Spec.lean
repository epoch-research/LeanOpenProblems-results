import FormalConjectures.Util.ProblemImports

open Nat

/--
A196698: Number of primes of the form $3^n \pm 3^k \pm 1$ with $0 \le k < n$.
-/
def A196698 (n : ℕ) : ℕ :=
  let p3n := 3 ^ n
  (Finset.range n).biUnion (fun k =>
    let p3k := 3 ^ k
    -- The four terms $3^n \pm 3^k \pm 1$:
    { p3n + p3k + 1,
      p3n + p3k - 1,
      p3n - p3k + 1,
      p3n - p3k - 1 }
  )
  |>.filter Nat.Prime
  |>.card



/--
Conjecture: infinitely many elements of this sequence are equal to 0.
-/
theorem oeis_196698_conjecture_2 : ∀ M : ℕ, ∃ n : ℕ, n > M ∧ A196698 n = 0 := by
  sorry
