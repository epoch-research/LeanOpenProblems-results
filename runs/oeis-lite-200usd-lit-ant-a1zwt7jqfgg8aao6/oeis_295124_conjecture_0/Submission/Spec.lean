import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
A295124: $a(n)$ is the smallest number $k$ with $n$ prime factors such that $2d + k/d$ is prime for every $d \mid k$.
The definition interprets "n prime factors" as $n$ distinct prime factors ($\omega(k) = n$).
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define the set of candidate numbers $k$ for a given $n$.
  let S (n : ℕ) : Set ℕ :=
    {k : ℕ | k > 0 ∧
      -- $\omega(k) = n$, k has n distinct prime factors.
      (Nat.primeFactors k).card = n ∧
      -- For every divisor d of k, $2d + k/d$ is prime.
      (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}

  -- $a(n)$ is the smallest element of this set. sInf is the infimum function on sets of ℕ.
  sInf (S n)

open scoped Pointwise

set_option maxRecDepth 8000

/-!
## Status of the conjecture (A295124)

This conjecture asserts that for every `n` there is a positive integer `k` with exactly `n`
distinct prime factors such that `2 * d + k / d` is prime for **every** divisor `d ∣ k`.

**Summary of the analysis.**  The statement is (almost certainly) *true* but is a genuinely
open problem, equivalent to a special case of **Dickson's conjecture** on the simultaneous
primality of a family of linear forms.  The key facts are:

* *Reduction to Dickson.*  Write a candidate as `k = p · m`, fixing the first `n-1` primes as
  `m` and letting `p` be the last prime.  The divisors of `k` are `d` and `d·p` for `d ∣ m`, and
  the `2ⁿ` forms `2·d' + k/d'` become **linear forms in `p`**:
  `{ (m/d)·p + 2d : d ∣ m } ∪ { 2d·p + (m/d) : d ∣ m }`.
  Requiring all of these to be simultaneously prime for a single `p` is exactly the content of
  Dickson's conjecture for that admissible tuple.

* *No local obstruction (hence not disprovable).*  For every prime `q ≥ 5`, taking all prime
  factors `≡ 1 (mod q)` makes every form `≡ 3 (mod q) ≠ 0`; for `q = 3`, taking an odd number of
  prime factors `≡ 2 (mod 3)` avoids the obstruction (and `q = 2` never divides an odd `k`).
  Thus the singular series is positive for suitable configurations, so solutions are expected
  for every `n` (indeed infinitely many).  There is no covering/parity obstruction for any `n`,
  so the negation cannot be proved either.

* *Not provable with current mathematics.*  Establishing even a single solution for `n ≥ 5`
  requires a positive lower bound for the simultaneous primality of ≥ 2ⁿ linear forms.  This is
  blocked by the **parity problem** of sieve theory — the same barrier that leaves the twin-prime
  and Sophie-Germain conjectures open (already `n = 1` encodes such a prime constellation).

* *Known data.*  Witnesses are known only for small `n`:
  `a(0)=1, a(1)=3, a(2)=15, a(3)=105, a(4)=93081`; the value `a(5)` is unknown and expected to
  be astronomically large — consistent with the OEIS author's remark "It is hard to believe!".

The proof below discharges the cases `n ≤ 3` with explicit witnesses.  The general case
`n ≥ 4` is precisely the open Dickson-type statement described above.
-/

/-- Conjecture: the sequence is infinite. It is hard to believe!
This is formalized as the set $S(n)$ of candidate numbers being non-empty for all $n$. -/
theorem oeis_295124_conjecture_0 :
  ∀ n : ℕ, (({k : ℕ | k > 0 ∧
              (Nat.primeFactors k).card = n ∧
              (∀ d, d ∈ Nat.divisors k → Nat.Prime (2 * d + k / d))}) : Set ℕ).Nonempty := by
  intro n
  match n with
  | 0 =>
    -- k = 1 : only divisor is 1, and 2*1 + 1 = 3 is prime.
    refine ⟨1, by norm_num, by simp, ?_⟩
    intro d hd
    simp only [Nat.divisors_one, Finset.mem_singleton] at hd
    subst hd; norm_num
  | 1 =>
    -- k = 3 : divisors 1, 3 give 5, 7.
    refine ⟨3, by norm_num, ?_, ?_⟩
    · rw [Nat.Prime.primeFactors (by norm_num)]; simp
    · intro d hd; fin_cases hd <;> norm_num
  | 2 =>
    -- k = 15 = 3·5 : divisors 1,3,5,15 give 17, 11, 13, 31.
    refine ⟨15, by norm_num, ?_, ?_⟩
    · rw [show (15 : ℕ) = 3 * 5 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
      decide
    · intro d hd; fin_cases hd <;> norm_num
  | 3 =>
    -- k = 105 = 3·5·7 : all eight divisor-forms are prime.
    refine ⟨105, by norm_num, ?_, ?_⟩
    · rw [show (105 : ℕ) = 3 * 5 * 7 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
         Nat.Prime.primeFactors (by norm_num)]
      decide
    · intro d hd; fin_cases hd <;> norm_num
  | 4 =>
    -- k = 93081 = 3·19·23·71 : all sixteen divisor-forms are prime (the last known witness).
    refine ⟨93081, by norm_num, ?_, ?_⟩
    · rw [show (93081 : ℕ) = 3 * 19 * 23 * 71 from rfl,
         Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.primeFactors_mul (by norm_num) (by norm_num),
         Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
         Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
      decide
    · have h : Nat.divisors 93081
          = Nat.divisors 3 * Nat.divisors 19 * Nat.divisors 23 * Nat.divisors 71 := by
        rw [← Nat.divisors_mul, ← Nat.divisors_mul, ← Nat.divisors_mul]
      rw [h, Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num),
          Nat.Prime.divisors (by norm_num), Nat.Prime.divisors (by norm_num)]
      intro d hd; fin_cases hd <;> norm_num
  | (m + 5) =>
    -- OPEN: this is the Dickson-type case (parity-problem barrier); see the discussion above.
    -- The smallest witness `a(5)` is unknown and expected to be astronomically large.
    sorry
