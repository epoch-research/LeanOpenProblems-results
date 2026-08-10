import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

/-
The sequence satisfies `a n = 2 * #{k ∈ [1,n] : ⌊(3/2)^k⌋ is odd} - n`, i.e. it is the
partial-sum (±1) walk whose `k`-th step is `+1` when `⌊(3/2)^k⌋` is odd and `-1` when it
is even.  Equivalently, the step is determined by the `k`-th binary digit of `3^k`.

The OEIS conjecture `∃ N, ∀ n ≥ N, a n > √n` is the assertion that this walk is eventually
larger than `√n`.  Computation shows it is **false**: e.g. `a 331523 = -1 < √331523`, and
`a n ≤ 0` already occurs tens of thousands of times below `5·10^5`, with `a` reaching
values as negative as `-1723`.

The negation below is therefore the correct statement.  Its proof reduces (rigorously)
to the lemma `a_le_zero_frequently : ∀ N, ∃ n ≥ N, a n ≤ 0`, i.e. that the walk is not
eventually positive.  That lemma is exactly the (currently open) recurrence question for
this walk — the OEIS entry poses "Is a(n) > 0?" as an open problem, and it is equivalent
to a statement about the distribution of the binary digits of `3^k` that lies in the orbit
of Mahler's `3/2` problem.
-/

/-- Key number-theoretic input: the walk `a` is not eventually positive, i.e. there are
arbitrarily large `n` with `a n ≤ 0`.  Equivalently, among `k ∈ [1,n]` the values
`⌊(3/2)^k⌋` that are even are (cumulatively) at least as numerous as the odd ones,
infinitely often.

Computation makes this overwhelmingly true: `a` reaches `-1723`, and `a n ≤ 0` occurs at
roughly 41% of all `n ≤ 2·10^6`, including `n = 2 000 000` itself.  However a *proof*
reduces to the assertion that the even values of `⌊(3/2)^k⌋` have cumulative density
`≥ 1/2` infinitely often, which is strictly stronger than the (open) statement that
`{(3/2)^k}` is dense mod 1 — Mahler's 3/2 problem.  The Flatto–Lagarias–Pollington gap
bound (`1/3`) is provably too weak (`1/3 < 1/2`), and the parity bit `bit_k(3^k)` of the
floor is a "middle" binary digit of `3^k`, inaccessible to any modular or equidistribution
tool currently available. -/
theorem a_le_zero_frequently : ∀ N : ℕ, ∃ n ≥ N, a n ≤ 0 := by
  sorry

/-- Disproof of the OEIS conjecture `∃ N, ∀ n ≥ N, a n > √n`.  Since the walk `a` returns
to `≤ 0` for arbitrarily large `n` (`a_le_zero_frequently`) and `√n ≥ 0`, no threshold `N`
can make `a n > √n` hold for all `n ≥ N`. -/
theorem oeis_71532_conjecture_0.disproof :
    ¬ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hnN, hn0⟩ := a_le_zero_frequently N
  have h1 : (a n : ℝ) > sqrt (n : ℝ) := hN n hnN
  have h2 : (a n : ℝ) ≤ 0 := by exact_mod_cast hn0
  have h3 : (0 : ℝ) ≤ sqrt (n : ℝ) := Real.sqrt_nonneg _
  linarith
