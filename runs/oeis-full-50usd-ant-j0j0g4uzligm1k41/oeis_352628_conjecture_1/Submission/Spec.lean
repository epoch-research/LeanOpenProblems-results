import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352628: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 2d^4 + 3c^2d^2$,
where $a,b,c,d$ are nonnegative integers.
-/
def A352628 (n : ℕ) : ℕ :=
  -- A sufficient bound for all variables.
  -- Note: c^4 and 2*d^4 are the largest terms, so c, d are roughly bounded by n^(1/4).
  -- range (n+1) is a very loose but safe upper bound.
  let S : Finset ℕ := range (n + 1)

  -- The search space is $S \times S \times S \times S$
  let Q := S.product (S.product (S.product S))

  -- The number of ways is the sum of 1 for each tuple that satisfies the equation.
  Q.sum fun p =>
    let a := p.fst
    let p_bcd := p.snd
    let b := p_bcd.fst
    let p_cd := p_bcd.snd
    let c := p_cd.fst
    let d := p_cd.snd

    -- Match the target equation exactly. The expression is equivalent to
    -- a^2 + 2*b^2 + (c^2 + d^2) * (c^2 + 2*d^2)
    let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
    if E = n then 1 else 0

/-- **Reduction lemma.** If `n` admits an in-range representation
`n = a^2 + 2b^2 + c^4 + 2d^4 + 3c^2 d^2` (with all variables `≤ n`), then the
counting function `A352628 n` is positive: the tuple `(a,b,c,d)` lies in the
search space `range (n+1)^4` and contributes `1` to the sum. -/
theorem A352628_pos_of_repr (n : ℕ)
    (h : ∃ a b c d : ℕ, a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n ∧
      a ^ 2 + 2 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n) :
    A352628 n > 0 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hE⟩ := h
  unfold A352628
  set S : Finset ℕ := range (n + 1) with hS
  have haS : a ∈ S := by rw [hS, mem_range]; omega
  have hbS : b ∈ S := by rw [hS, mem_range]; omega
  have hcS : c ∈ S := by rw [hS, mem_range]; omega
  have hdS : d ∈ S := by rw [hS, mem_range]; omega
  have hpQ : (a, b, c, d) ∈ S.product (S.product (S.product S)) :=
    Finset.mem_product.mpr ⟨haS, Finset.mem_product.mpr ⟨hbS,
      Finset.mem_product.mpr ⟨hcS, hdS⟩⟩⟩
  apply Finset.sum_pos'
  · intro i _; positivity
  · refine ⟨(a, b, c, d), hpQ, ?_⟩
    show 0 < (if a ^ 2 + 2 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n then 1 else 0)
    rw [if_pos hE]
    exact Nat.one_pos

/-- **Existence of a representation** (the number-theoretic core of A352628).

By the reduction lemma, `A352628 n > 0` is equivalent to the existence of
nonnegative integers `a, b, c, d` with
`n = a^2 + 2b^2 + c^4 + 2d^4 + 3c^2 d^2 = a^2 + 2b^2 + (c^2+d^2)(c^2+2d^2)`. -/
theorem A352628_repr_exists (n : ℕ) :
    ∃ a b c d : ℕ, a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n ∧
      a ^ 2 + 2 * b ^ 2 + c ^ 4 + 2 * d ^ 4 + 3 * c ^ 2 * d ^ 2 = n := by
  sorry

/--
Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as a^2 + 2b^2 + (c^2+d^2)*(c^2+2d^2) with a,b,c,d integers.
-/
theorem oeis_352628_conjecture_1 (n : ℕ) : A352628 n > 0 :=
  A352628_pos_of_repr n (A352628_repr_exists n)
