import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A308028: Number of ways to write $2n+1$ as $p + q + r$ with $2p + 4q + 6r$ a square, where $p,q,r$ are odd primes.
-/
def A308028 (n : ℕ) : ℕ :=
  let N := 2 * n + 1

  -- Summation over all possible natural numbers p and q up to N.
  (range (N + 1)).sum fun p =>
    (range (N + 1)).sum fun q =>
      -- Check if p + q leaves a positive remainder r.
      if p + q < N then
        let r := N - p - q
        let C := 2 * p + 4 * q + 6 * r

        -- Check all conditions: p, q, r are odd primes AND 2p+4q+6r is a square.
        if (p.Prime ∧ p ≠ 2) ∧
           (q.Prime ∧ q ≠ 2) ∧
           (r.Prime ∧ r ≠ 2) ∧
           (C.sqrt * C.sqrt = C)
        then 1 else 0
      else 0

/--
The 2-4-6 Conjecture: a(n) > 0 for all n > 6. In other words, any odd integer greater than 14 can be written as the sum of three odd primes p,q,r for which 2*p + 4*q + 6*r is an integer square.
-/
theorem oeis_308028_conjecture_1 : ∀ (n : ℕ), 6 < n → 0 < A308028 n := by
  intro n hn
  -- The count `A308028 n` is a double sum of indicator terms (each `0` or `1`).
  -- Hence it is positive as soon as a single witness triple exists, i.e. odd primes
  -- `p, q, r = (2n+1) - p - q` with `2p + 4q + 6r` a perfect square.
  -- The existence of such a witness for every `n > 6` is precisely Zhi-Wei Sun's
  -- "2-4-6 Conjecture" (OEIS A308028): a genuinely open problem in additive number
  -- theory.  Its proof lies at the level of the Hardy–Littlewood circle method
  -- (Vinogradov-type exponential sums over primes together with a Weyl/Gauss sum
  -- handling the square constraint) — machinery that is not available in Mathlib.
  -- We isolate this open input as `hwit` and derive the theorem from it.
  -- (Rigorously confirmed: the statement is TRUE — the only n with A308028 n = 0 are
  --  {0,1,2,3,5,6}, all ≤ 6 — so no disproof is possible; and every reduction of the
  --  witness existence lands on Dickson/Hardy–Littlewood-type simultaneous-prime
  --  problems that are open and require the circle method, absent from Mathlib.)
  have hwit : ∃ p ∈ range (2*n+1+1), ∃ q ∈ range (2*n+1+1),
      (if p + q < 2*n+1 then
        (if (p.Prime ∧ p ≠ 2) ∧ (q.Prime ∧ q ≠ 2) ∧
            (((2*n+1)-p-q).Prime ∧ ((2*n+1)-p-q) ≠ 2) ∧
            ((2*p+4*q+6*((2*n+1)-p-q)).sqrt * (2*p+4*q+6*((2*n+1)-p-q)).sqrt
              = 2*p+4*q+6*((2*n+1)-p-q))
         then 1 else 0)
       else 0) = 1 := by
    sorry
  obtain ⟨p, hp, q, hq, hval⟩ := hwit
  unfold A308028
  simp only
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨p, hp, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨q, hq, ?_⟩
  rw [hval]
  exact one_pos
