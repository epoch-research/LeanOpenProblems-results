import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A352627: Number of ways to write $n$ as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$,
where $a, b, c, d$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let R : Finset ℕ := Finset.range (sqrt n + 1)
  /-
  A tuple (a, b, c, d) where a, b, c, d are in R.
  We use nested products: R x (R x (R x R))
  -/
  let S_quadruples := R.product (R.product (R.product R))

  (S_quadruples.filter (fun p =>
    let a := p.1;
    let b := p.2.1;
    let c := p.2.2.1;
    let d := p.2.2.2;
    a^2 + 2 * b^2 + c^4 + 4 * d^4 + c^2 * d^2 = n
  )).card

/--
A352627 Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each nonnegative integer can be written as $a^2 + 2b^2 + c^4 + 4d^4 + c^2d^2$ with a,b,c,d integers.
-/
theorem oeis_352627_conjecture_0 : ∀ (n : ℕ), a n > 0 := by
  intro n
  -- Reduction: since any solution `(x,y,z,w)` to the equation automatically satisfies
  -- `x,y,z,w ≤ sqrt n` (each summand is `≤ n`), the counting function `a n` is positive
  -- exactly when `n` admits a representation of the required shape.  This reduction is
  -- proven in full below; it remains to establish the existence of a representation.
  suffices h : ∃ x y z w : ℕ, x^2 + 2*y^2 + z^4 + 4*w^4 + z^2*w^2 = n by
    obtain ⟨x, y, z, w, hxyzw⟩ := h
    rw [a]
    simp only
    rw [gt_iff_lt, Finset.card_pos]
    refine ⟨(x, y, z, w), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, hxyzw⟩
    have hz2 : z^2 ≤ z^4 := by
      rcases Nat.eq_zero_or_pos z with h|h
      · simp [h]
      · exact Nat.pow_le_pow_right h (by norm_num)
    have hw2 : w^2 ≤ 4*w^4 := by
      have hle : w^2 ≤ w^4 := by
        rcases Nat.eq_zero_or_pos w with h|h
        · simp [h]
        · exact Nat.pow_le_pow_right h (by norm_num)
      omega
    have hx : x ≤ sqrt n := by
      rw [Nat.le_sqrt]
      nlinarith [hxyzw, Nat.zero_le (y^2), Nat.zero_le (z^4), Nat.zero_le (w^4), Nat.zero_le (z^2*w^2)]
    have hy : y ≤ sqrt n := by
      rw [Nat.le_sqrt]
      nlinarith [hxyzw, Nat.zero_le (x^2), Nat.zero_le (z^4), Nat.zero_le (w^4), Nat.zero_le (z^2*w^2)]
    have hz : z ≤ sqrt n := by
      rw [Nat.le_sqrt]
      nlinarith [hxyzw, Nat.zero_le (x^2), Nat.zero_le (y^2), Nat.zero_le (w^4), Nat.zero_le (z^2*w^2), hz2]
    have hw : w ≤ sqrt n := by
      rw [Nat.le_sqrt]
      nlinarith [hxyzw, Nat.zero_le (x^2), Nat.zero_le (y^2), Nat.zero_le (z^4), Nat.zero_le (z^2*w^2), hw2]
    have hxr : x ∈ range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hyr : y ∈ range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hzr : z ∈ range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    have hwr : w ∈ range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
    exact Finset.mk_mem_product hxr (Finset.mk_mem_product hyr (Finset.mk_mem_product hzr hwr))
  sorry
