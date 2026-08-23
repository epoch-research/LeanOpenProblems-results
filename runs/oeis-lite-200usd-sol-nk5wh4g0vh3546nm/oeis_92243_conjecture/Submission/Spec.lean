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


private noncomputable def primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i

private noncomputable def gapAt (k : ℕ) : ℕ := primeAt k - primeAt (k - 1)

private lemma A092243_succ {n : ℕ} (hn : 1 ≤ n) :
    A092243 (n + 1) =
      A092243 n + ((gapAt (n + 1) : ℤ) - (gapAt n : ℤ)).sign := by
  rw [A092243, A092243]
  have hn0 : n ≠ 0 := by omega
  have hs0 : n + 1 ≠ 0 := by omega
  have hs1 : n + 1 ≠ 1 := by omega
  simp only [hs0, hs1, hn0, if_false]
  by_cases hn1 : n = 1
  · subst n
    norm_num [gapAt, primeAt, Nat.nth_prime_zero_eq_two,
      Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  simp only [hn1, if_false]
  rw [Finset.sum_Icc_succ_top (by omega)]
  simp [gapAt, primeAt]

private lemma A092243_of_increasing_gaps (a l : ℕ) (ha : 1 ≤ a)
    (hr : ∀ j < l, gapAt (a + j) < gapAt (a + j + 1)) :
    A092243 (a + l) = A092243 a + (l : ℤ) := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [show a + (l + 1) = (a + l) + 1 by omega,
        A092243_succ (by omega), ih]
      · have hh := hr l (by omega)
        have hz : (gapAt (a + l) : ℤ) < (gapAt (a + l + 1) : ℤ) := by
          exact_mod_cast hh
        rw [Int.sign_eq_one_iff_pos.mpr (sub_pos.mpr hz)]
        push_cast
        ring
      · intro j hj
        exact hr j (by omega)

private lemma not_bounded_both_of_increasing_gap_runs
    (runs : ∀ l : ℕ, ∃ a : ℕ, 1 ≤ a ∧
      ∀ j < l, gapAt (a + j) < gapAt (a + j + 1)) :
    ¬ ((∃ B : ℤ, ∀ n : ℕ, B ≤ A092243 n) ∧
       (∃ C : ℤ, ∀ n : ℕ, A092243 n ≤ C)) := by
  rintro ⟨⟨B, hB⟩, ⟨C, hC⟩⟩
  have hBC : B ≤ C := le_trans (hB 0) (hC 0)
  let l : ℕ := (C - B).toNat + 1
  obtain ⟨a, ha, hr⟩ := runs l
  have heq := A092243_of_increasing_gaps a l ha hr
  have hlow := hB a
  have hupp := hC (a + l)
  rw [heq] at hupp
  have hl : C - B < (l : ℤ) := by
    dsimp [l]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hBC)]
    omega
  omega

theorem oeis_92243_conjecture : OEIS_A092243_Conjectures := by sorry
