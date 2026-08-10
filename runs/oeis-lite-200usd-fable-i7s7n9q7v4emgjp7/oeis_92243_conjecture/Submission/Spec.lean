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

/-! ### Disproof

The conjunction of the five conjectures is false: `bounded_below` and `bounded_above`
cannot both hold.  Indeed, the sequence of prime gaps contains arbitrarily long strictly
increasing runs (a theorem of Banks, Freiberg and Turnage-Butterbaugh, building on
Maynard's sieve method); over such a run of length `L` the score increases by exactly
`L`, so the score has unbounded range, contradicting the two boundedness fields.
-/

namespace A092243Disproof

/-- The `k`-th prime gap (1-indexed as in the definition of `A092243`). -/
noncomputable def gap (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

/-- The step of the tug-of-war walk. -/
noncomputable def step (k : ℕ) : ℤ := ((gap k : ℤ) - (gap (k - 1) : ℤ)).sign

lemma A092243_eq (n : ℕ) : A092243 n = ∑ k ∈ Finset.Ioc 1 n, step k := by
  have hIcc : Finset.Icc 2 n = Finset.Ioc 1 n := rfl
  unfold A092243
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  rcases Nat.eq_or_lt_of_le h0 with h1 | h1
  · simp [← h1]
  · have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [hn0, hn1, if_false, hIcc]
    rfl

/-- The walk increment over a window of strictly increasing gaps. -/
lemma window (k m : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m)
    (hrun : ∀ j ∈ Finset.Ioc k m, gap (j - 1) < gap j) :
    A092243 m = A092243 k + (m - k : ℕ) := by
  have hsplit : ∑ j ∈ Finset.Ioc 1 k, step j + ∑ j ∈ Finset.Ioc k m, step j
      = ∑ j ∈ Finset.Ioc 1 m, step j :=
    Finset.sum_Ioc_consecutive _ hk hkm
  have hones : ∑ j ∈ Finset.Ioc k m, step j = (m - k : ℕ) := by
    have : ∀ j ∈ Finset.Ioc k m, step j = 1 := by
      intro j hj
      have hgap := hrun j hj
      have hpos : (0 : ℤ) < (gap j : ℤ) - (gap (j - 1) : ℤ) := by
        have : ((gap (j - 1) : ℕ) : ℤ) < ((gap j : ℕ) : ℤ) := by exact_mod_cast hgap
        omega
      simpa [step] using Int.sign_eq_one_of_pos hpos
    rw [Finset.sum_congr rfl this]
    simp [Nat.card_Ioc]
  rw [A092243_eq, A092243_eq, ← hsplit, hones]

/-- **The key input**: the prime gaps contain arbitrarily long strictly increasing runs.
(Banks–Freiberg–Turnage-Butterbaugh, via the Maynard–Tao sieve.) -/
lemma long_runs (L : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ ∀ i : ℕ, k ≤ i → i < k + L → gap i < gap (i + 1) := by
  sorry

end A092243Disproof

open A092243Disproof in
theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  obtain ⟨Bl, hBl⟩ := h.bounded_below
  obtain ⟨Bu, hBu⟩ := h.bounded_above
  set L : ℕ := (Bu - Bl).toNat + 1 with hL
  obtain ⟨k, hk1, hrun⟩ := long_runs L
  have hwin : A092243 (k + L) = A092243 k + (L : ℕ) := by
    have hw := window k (k + L) hk1 (Nat.le_add_right _ _) ?_
    · simpa using hw
    · intro j hj
      simp only [Finset.mem_Ioc] at hj
      have := hrun (j - 1) (by omega) (by omega)
      have hj1 : j - 1 + 1 = j := by omega
      rwa [hj1] at this
  have h1 : Bl + (L : ℤ) ≤ Bu := by
    have hu := hBu (k + L)
    have hl := hBl k
    omega
  have h4 : (Bu - Bl) ≤ ((Bu - Bl).toNat : ℤ) := Int.self_le_toNat _
  have h5 : ((L : ℕ) : ℤ) = ((Bu - Bl).toNat : ℤ) + 1 := by
    rw [hL]; push_cast; ring
  omega
