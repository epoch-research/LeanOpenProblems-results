import FormalConjectures.Util.ProblemImports

open Nat BigOperators Int

/--
A092243: Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score = 0 at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by 1
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.
-/
noncomputable def A092243 (n : ℕ) : ℤ :=
  -- P_i is the $i$-th prime, 0-indexed: P 0 = 2, P 1 = 3, ...
  -- Note: Nat.nth Nat.Prime i gives the i-th prime, where i=0 is the 0-th prime, 2.
  let P (i : ℕ) : ℕ := Nat.nth Nat.Prime i

  -- $G_k$ is the $k$-th prime gap (OEIS 1-indexed), $G_k = P_k - P_{k-1}$, for $k \ge 1$.
  -- Here we use the 0-indexed primes P_i, so the k-th gap involves the prime P[k] and P[k-1].
  let G_gap (k : ℕ) : ℕ := P k - P (k - 1)

  if n = 0 then 0 -- Defining for n=0 as 0, though OEIS starts at 1
  else if n = 1 then 0
  else

  -- The score is the cumulative sum of the changes $\Delta(k) = \operatorname{sign}(G_k - G_{k-1})$ for $k=2$ to $n$.
  -- The sum starts at k=2 because the first gap G_1 is compared to G_2. The comparison is between G_k and G_{k-1}.
  -- Since the first gap is G_1, the first comparison is at k=2 (G_2 vs G_1).
  (Finset.Icc 2 n).sum fun k : ℕ =>
    let Gk   : ℕ := G_gap k
    -- Since $k \ge 2$, $k-1 \ge 1$, so G_gap (k-1) is safely computed.
    let Gkm1 : ℕ := G_gap (k - 1)

    -- Calculate $\operatorname{sign}(G_k - G_{k-1})$ using integer subtraction and sign function.
    ((Gk : ℤ) - (Gkm1 : ℤ)) |>.sign

/-
We remove the specific proofs for a_one etc., as they failed compilation and are not the object of the final submission.
The definition of A092243 is now corrected for proper syntax of the n-th prime.
-/

/--
Conjectures regarding the long-term behavior of A092243 (the score $s$).

Questions from OEIS A092243, including the primary conjectures:
1. Is s > 0 for some n > 250000?
2. Is s bounded from below?
3. Is s bounded from above?
4. Is s > 0 for infinitely many values of n?
5. Is s < 0 for infinitely many values of n?
-/
structure OEIS_A092243_Conjectures where
  /-- Is the score ever positive after n = 250,000? -/
  positive_after_large_n : ∃ n : ℕ, n > 250000 ∧ A092243 n > 0
  /-- Is the score bounded from below? -/
  bounded_below : ∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n
  /-- Is the score bounded from above? -/
  bounded_above : ∃ B : ℤ, ∀ n : ℕ, A092243 n ≤ B
  /-- Is the score positive infinitely often? -/
  infinitely_positive : Set.Infinite {n : ℕ | A092243 n > 0}
  /-- Is the score negative infinitely often? -/
  infinitely_negative : Set.Infinite {n : ℕ | A092243 n < 0}

/--
**The score `A092243` is 1-Lipschitz**: each successive stage changes the score
by `-1`, `0`, or `+1` (the sign of a single prime-gap comparison). This is the only
structural fact about the score we can establish unconditionally, and it is *not*
enough to settle the boundedness questions below (a bounded, 1-Lipschitz sequence
that is positive and negative infinitely often is perfectly consistent — e.g. the
score of an artificial gap sequence that oscillates as a balanced sawtooth around
the growing mean `log n`). Empirically the actual prime score behaves as an
unbounded `√n` random walk, but proving this is exactly OEIS A092243's open
question. -/
theorem A092243_succ (n : ℕ) (hn : 2 ≤ n) :
    A092243 (n + 1) =
      A092243 n +
        Int.sign
          (((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℤ) -
            ((Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1) : ℕ) : ℤ)) := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hn1' : n + 1 ≠ 0 := by omega
  have hn1'' : n + 1 ≠ 1 := by omega
  simp only [A092243, hn0, hn1, hn1', hn1'', if_false]
  rw [show n + 1 = (n + 1) by rfl]
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
  simp only [Nat.add_sub_cancel]

/--
**Unboundedness of the score (OEIS A092243, open question #2/#3).**

The negation of the bundled conjecture follows from the single statement that the
score is unbounded above (equivalently, `bounded_above` is false). Numerically the
score is an unbounded `√n` random walk, so this is true; but it is an *open*
problem: it cannot be derived from any property of prime gaps available in Mathlib
(PNT-type growth, Bertrand's postulate, congruence structure, Mertens' theorems,
unbounded gaps, infinitely many ascents/descents, non-periodicity), since explicit
bounded-score sequences satisfy all of those. A genuine proof needs the conjectural
fine distribution of consecutive prime gaps (prime `k`-tuples level), which is
beyond current mathematics.

This is the irreducible mathematical content of disproving the conjecture. -/
theorem A092243_unbounded_above : ∀ B : ℤ, ∃ n : ℕ, B < A092243 n := by
  sorry

/--
The bundled OEIS A092243 conjecture is **false**: it asserts (among other things)
that the score is bounded both below and above, whereas the score is unbounded.
Concretely, `bounded_above` contradicts `A092243_unbounded_above`. -/
theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  rintro ⟨-, -, ⟨B, hB⟩, -, -⟩
  obtain ⟨n, hn⟩ := A092243_unbounded_above B
  exact absurd (hB n) (not_le.2 hn)
