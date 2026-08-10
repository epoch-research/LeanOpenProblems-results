import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  let S_quadruples := R.product (R.product (R.product R)) -- Represents a set of $\mathbb{N}^4$ tuples

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  intro n
  -- Reduction: it suffices to exhibit *any* representation; the search bound `sqrt n`
  -- is provably large enough to contain the witnesses (a^2 ≤ n ⇒ a ≤ sqrt n, etc.).
  suffices h : ∃ A B C D : ℕ, A ^ 2 + 2 * B ^ 2 + C ^ 4 + 4 * D ^ 4 + C ^ 2 * D ^ 2 = n by
    obtain ⟨A, B, C, D, hABCD⟩ := h
    rw [a]; simp only; rw [Finset.card_pos]
    refine ⟨(A, (B, (C, D))), ?_⟩
    rw [Finset.mem_filter]
    have memR : ∀ x : ℕ, x * x ≤ n → x ∈ Finset.range (sqrt n + 1) := by
      intro x hx; rw [Finset.mem_range, Nat.lt_succ_iff]; exact Nat.le_sqrt.mpr hx
    have hA : A ∈ Finset.range (sqrt n + 1) := by
      apply memR
      nlinarith [hABCD, sq_nonneg B, Nat.zero_le (C ^ 4), Nat.zero_le (4 * D ^ 4),
        Nat.zero_le (C ^ 2 * D ^ 2)]
    have hB : B ∈ Finset.range (sqrt n + 1) := by
      apply memR
      nlinarith [hABCD, sq_nonneg A, Nat.zero_le (C ^ 4), Nat.zero_le (4 * D ^ 4),
        Nat.zero_le (C ^ 2 * D ^ 2)]
    have hC : C ∈ Finset.range (sqrt n + 1) := by
      apply memR
      rcases Nat.eq_zero_or_pos C with hc | hc
      · simp [hc]
      · nlinarith [hABCD, sq_nonneg A, sq_nonneg B, Nat.zero_le (4 * D ^ 4),
          Nat.zero_le (C ^ 2 * D ^ 2), hc, sq_nonneg C]
    have hD : D ∈ Finset.range (sqrt n + 1) := by
      apply memR
      rcases Nat.eq_zero_or_pos D with hd | hd
      · simp [hd]
      · nlinarith [hABCD, sq_nonneg A, sq_nonneg B, Nat.zero_le (C ^ 4),
          Nat.zero_le (C ^ 2 * D ^ 2), hd, sq_nonneg D]
    exact ⟨Finset.mem_product.mpr ⟨hA, Finset.mem_product.mpr ⟨hB,
      Finset.mem_product.mpr ⟨hC, hD⟩⟩⟩, by simpa using hABCD⟩
  -- Remaining core: every nonnegative integer is represented.  This is the open
  -- analytic conjecture (Z.-W. Sun, OEIS A352627); see analysis notes.
  sorry
