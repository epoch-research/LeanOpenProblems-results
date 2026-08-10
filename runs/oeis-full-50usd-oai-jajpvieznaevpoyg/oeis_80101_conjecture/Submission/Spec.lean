import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A080101: Number of prime powers in all composite numbers between $n$-th prime and next prime.
Let $p_n$ be the $n$-th prime. $a(n)$ is the number of prime powers $k$ such that $p_n < k < p_{n+1}$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : 0 < n then
    -- $p_n$ (the n-th prime in OEIS 1-indexing) corresponds to Nat.nth Nat.Prime (n - 1) in Mathlib's 0-indexing.
    let p_n := Nat.nth Nat.Prime (n - 1)
    -- $p_{n+1}$ is Nat.nth Nat.Prime n.
    let p_succ_n := Nat.nth Nat.Prime n

    -- We count the number of prime powers in the open interval (p_n, p_{n+1}).
    -- IsPrimePow is the correct predicate, globally available through Mathlib.
    (Ioo p_n p_succ_n).filter IsPrimePow |>.card
  else
    0

/--
A080101: The maximum value of terms in the sequence is conjectured to be 2.
This is a formalization of the OEIS conjecture: "The maximum value of terms in the sequence, through the (10^5)th term, is 2. - Harvey P. Dale, Aug 24 2014 This is conjectured to be the maximum, see also A366833. - Gus Wiseman, Nov 06 2024"
-/
theorem oeis_80101_conjecture : ∀ (n : ℕ), a n ≤ 2 := by sorry
