import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A308950: Number of ways to write $n$ as $(p-1)/6 + 2^a 3^b$, where $p$ is a prime, and $a$ and $b$ are nonnegative integers.
$a(n)$ is the number of pairs $(a, b) \in \mathbb{N}^2$ such that $2^a 3^b \le n$ and $6(n - 2^a 3^b) + 1$ is prime.
-/
noncomputable def A308950 (n : ℕ) : ℕ :=
  Finset.card $
    (Finset.range (n + 1)).product (Finset.range (n + 1)) |>.filter
    (fun p_ab =>
      let a := p_ab.fst
      let b := p_ab.snd
      let m := 2 ^ a * 3 ^ b
      m ≤ n ∧
      Nat.Prime (6 * (n - m) + 1)
    )

theorem oeis_308950_conjecture :
  ∀ n : ℕ, 1 < n →
    (∃ (a b : ℕ),
        2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)
    )
    ∨
    (∃ (a b : ℕ),
        2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)
    ) := by
  sorry

theorem oeis_308950_conjecture.disproof : ¬ (type_of% @oeis_308950_conjecture) := by
  sorry
