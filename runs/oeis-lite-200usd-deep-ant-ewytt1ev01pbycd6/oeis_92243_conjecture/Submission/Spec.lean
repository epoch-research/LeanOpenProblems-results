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
`A092243` has arbitrarily large *rises*: for every `m` there are indices `a ≤ b` at which the
score increases by exactly `m`, i.e. `A092243 b = A092243 a + m`.

This is a genuine (non-open!) theorem of analytic number theory.  The consecutive prime gaps
`g_k = p_k - p_{k-1}` contain **arbitrarily long strictly increasing runs**: for every `m` there
are `m + 1` consecutive primes with `g_n < g_{n+1} < ⋯ < g_{n+m}`.  Along such a run every summand
`sign(g_{k} - g_{k-1})` equals `+1`, so the partial sum `A092243` increases by `1` at each of the
`m` steps and hence rises by exactly `m` over the run (take `a = n`, `b = n + m`).

The existence of arbitrarily long strictly increasing runs of consecutive prime gaps is a proven
theorem (J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015); W. Banks, T. Freiberg,
C. Turnage-Butterbaugh, *Consecutive primes in tuples*, Acta Arith. 167 (2015); W. Banks,
T. Freiberg, J. Maynard, *Limit points of the sequence of normalized prime gaps*, Proc. LMS (2016)).
Its proof requires the Maynard–Tao multidimensional sieve, which is **not** available in Mathlib and
is not reconstructible from elementary tools (even runs of length `3` are not known by elementary
means; Erdős–Turán 1948 only yields runs of length `2`, i.e. individual sign changes).  Hence this
lemma cannot currently be discharged inside Mathlib; it is the single, precisely-isolated
non-elementary input on which the disproof below rests. -/
theorem A092243_arbitrarily_large_rises :
    ∀ m : ℕ, ∃ a b : ℕ, A092243 a + (m : ℤ) = A092243 b := by
  sorry

/--
Disproof of `OEIS_A092243_Conjectures`.

The five bundled OEIS questions cannot all have answer "yes".  Assuming the score `A092243` were
bounded below by `B` and above by `C`, every rise `A092243 b - A092243 a` would be at most `C - B`.
But by `A092243_arbitrarily_large_rises` there is a rise of size `(C - B).toNat + 1 > C - B`, a
contradiction.  (Equivalently: a strictly increasing run of `> C - B` consecutive prime gaps forces
the score above its supposed upper bound `C`.)  This refutes `bounded_below ∧ bounded_above`, hence
the whole conjunction. -/
theorem oeis_92243_conjecture.disproof : ¬ OEIS_A092243_Conjectures := by
  rintro ⟨-, ⟨B, hB⟩, ⟨C, hC⟩, -, -⟩
  have hBC : B ≤ C := le_trans (hB 0) (hC 0)
  obtain ⟨a, b, hab⟩ := A092243_arbitrarily_large_rises ((C - B).toNat + 1)
  have hcast : ((((C - B).toNat + 1 : ℕ)) : ℤ) = C - B + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ C - B)]
  rw [hcast] at hab
  have h1 : B ≤ A092243 a := hB a
  have h2 : A092243 b ≤ C := hC b
  linarith
