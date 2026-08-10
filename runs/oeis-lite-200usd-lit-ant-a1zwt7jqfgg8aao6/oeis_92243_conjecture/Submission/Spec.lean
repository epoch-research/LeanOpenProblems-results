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

/-!
## Resolution: the conjecture is **false**.

The bundled conjecture asserts (among other things) that the score `A092243` is
bounded both below and above.  In fact the score is **unbounded**, so the field
`bounded_above` (and likewise `bounded_below`) fails, and the whole conjunction is false.

Unboundedness follows from the theorem of Banks–Freiberg–Turnage-Butterbaugh (2013),
which resolved a question of Erdős and Turán: the sequence of gaps between consecutive
primes contains **arbitrarily long strictly increasing runs**.  Concretely, if
`G k = p_k - p_{k-1}` denotes the `k`-th prime gap, then for every `L` there is a
starting index `a ≥ 1` with `G a < G (a+1) < ⋯ < G (a+L)`.

Given such a run, every comparison `term k = sign (G k - G (k-1))` along the run equals
`+1`, so the score jumps by exactly `L`:  `A092243 (a+L) = A092243 a + L`.  If the score
were bounded in `[B_lo, B_hi]`, then taking `L = (B_hi - B_lo) + 1` and using
`A092243 a ≥ B_lo` would give `A092243 (a+L) ≥ B_lo + L > B_hi`, contradicting the upper
bound.  Hence `A092243` is unbounded and the conjecture is false.

All of the reasoning below is fully verified except the single deep number-theoretic
input `runs`, which is the Banks–Freiberg–Turnage-Butterbaugh theorem.  Its proof uses the
Maynard–Tao method (multidimensional sieve + Bombieri–Vinogradov) and is not available in
Mathlib; there is no elementary proof (the pattern `2,4,2,6,2,8,…` shows that unboundedness
of the gaps alone does not force long monotone runs).
-/

/-- The `k`-th prime gap `p_k - p_{k-1}` (using `0`-indexed primes `p_i = Nat.nth Nat.Prime i`). -/
noncomputable def A092243.G (k : ℕ) : ℕ := Nat.nth Nat.Prime k - Nat.nth Nat.Prime (k - 1)

/-- The per-stage increment `sign (G k - G (k-1)) ∈ {-1, 0, 1}`. -/
noncomputable def A092243.term (k : ℕ) : ℤ :=
  ((A092243.G k : ℤ) - (A092243.G (k - 1) : ℤ)).sign

open A092243 in
/-- `A092243 n` is the partial sum of the increments over `Finset.Icc 2 n` (for every `n`,
including the degenerate `n = 0, 1` cases where both sides are the empty sum `0`). -/
theorem A092243.eq_sum (n : ℕ) : A092243 n = (Finset.Icc 2 n).sum A092243.term := by
  unfold A092243 A092243.term A092243.G
  rcases n with _ | _ | n
  · simp
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]

open A092243 in
/-- Over a strictly increasing run of gaps `G a < G (a+1) < ⋯ < G (a+L)` the score increases
by exactly `L`. -/
theorem A092243.run_jump (a L : ℕ) (ha : 1 ≤ a)
    (hrun : ∀ k, a < k → k ≤ a + L → A092243.G (k - 1) < A092243.G k) :
    A092243 (a + L) = A092243 a + (L : ℤ) := by
  rw [A092243.eq_sum, A092243.eq_sum]
  have h1 : Finset.Icc 2 (a + L) = Finset.Ioc 1 (a + L) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have h2 : Finset.Icc 2 a = Finset.Ioc 1 a := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h1, h2, ← Finset.sum_Ioc_consecutive A092243.term (by omega : 1 ≤ a)
      (by omega : a ≤ a + L)]
  have hsum : (Finset.Ioc a (a + L)).sum A092243.term = (L : ℤ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℤ))]
    · simp [Nat.card_Ioc]
    · intro k hk
      rw [Finset.mem_Ioc] at hk
      unfold A092243.term
      rw [Int.sign_eq_one_iff_pos]
      have h3 : (A092243.G (k - 1) : ℤ) < (A092243.G k : ℤ) := by
        exact_mod_cast hrun k hk.1 hk.2
      omega
  rw [hsum]

/-- **Banks–Freiberg–Turnage-Butterbaugh (2013).** The gaps between consecutive primes
contain arbitrarily long strictly increasing runs: for every `L` there is `a ≥ 1` with
`G a < G (a+1) < ⋯ < G (a+L)`.  (Resolves a question of Erdős–Turán; proved via Maynard–Tao.
Not available in Mathlib, and provably not elementary.) -/
theorem A092243.runs (L : ℕ) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ k, a < k → k ≤ a + L → A092243.G (k - 1) < A092243.G k := by
  sorry

open A092243 in
/-- The conjecture is false: the score is unbounded, contradicting `bounded_above`. -/
theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  intro h
  obtain ⟨Blo, hlo⟩ := h.bounded_below
  obtain ⟨Bhi, hhi⟩ := h.bounded_above
  obtain ⟨a, ha1, hrun⟩ := A092243.runs ((Bhi - Blo).toNat + 1)
  set L : ℕ := (Bhi - Blo).toNat + 1 with hL
  have hjump : A092243 (a + L) = A092243 a + (L : ℤ) := A092243.run_jump a L ha1 hrun
  have h1 : Blo ≤ A092243 a := hlo a
  have h2 : A092243 (a + L) ≤ Bhi := hhi (a + L)
  have hle : Blo ≤ Bhi := le_trans (hlo 0) (hhi 0)
  have key : Blo + (L : ℤ) ≤ Bhi := by
    calc Blo + (L : ℤ) ≤ A092243 a + L := by linarith
      _ = A092243 (a + L) := hjump.symm
      _ ≤ Bhi := h2
  have hcast : (L : ℤ) = Bhi - Blo + 1 := by
    rw [hL]; push_cast [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ Bhi - Blo)]; ring
  rw [hcast] at key
  omega
