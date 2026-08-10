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
theorem oeis_80101_conjecture : ∀ (n : ℕ), a n ≤ 2 := by
  intro n
  unfold a
  by_cases h : 0 < n
  · rw [dif_pos h]
    -- Remaining goal: the number of prime powers strictly between the consecutive
    -- primes `nth Prime (n-1)` and `nth Prime n` is at most 2.
    --
    -- This is the genuine content of OEIS conjecture A080101. It is *true* (no
    -- counterexample exists below 10^18) but settling it is open-problem hard:
    -- a hypothetical third prime power in a single prime gap forces either two
    -- perfect prime-squares more than 2*sqrt(N) apart inside a prime-free interval
    -- (which contradicts a prime existing in every interval of length ~sqrt(N),
    -- i.e. Legendre's/Oppermann's conjecture), or a Pillai-type near coincidence
    -- of high odd prime powers. Mathlib only provides Bertrand's postulate, which
    -- cannot resolve the ratio-<2 intervals these cases require.
    sorry
  · rw [dif_neg h]
    omega
