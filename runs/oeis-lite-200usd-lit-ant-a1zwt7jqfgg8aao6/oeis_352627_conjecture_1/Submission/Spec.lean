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

/-- The counting function `a n` is positive iff `n` admits a representation
`w^2 + 2*x^2 + y^4 + 4*z^4 + y^2*z^2 = n` with all variables bounded by `sqrt n`.
This is a faithful unfolding of the `Finset`-based definition. -/
theorem a_pos_iff (n : ℕ) : 0 < a n ↔
    ∃ w x y z : ℕ, w ≤ sqrt n ∧ x ≤ sqrt n ∧ y ≤ sqrt n ∧ z ≤ sqrt n ∧
      w ^ 2 + 2 * x ^ 2 + y ^ 4 + 4 * z ^ 4 + y ^ 2 * z ^ 2 = n := by
  unfold a
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨p, hp, heq⟩
    obtain ⟨hw, hp⟩ := Finset.mem_product.mp hp
    obtain ⟨hx, hp⟩ := Finset.mem_product.mp hp
    obtain ⟨hy, hz⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_range, Nat.lt_succ_iff] at hw hx hy hz
    exact ⟨p.1, p.2.1, p.2.2.1, p.2.2.2, hw, hx, hy, hz, heq⟩
  · rintro ⟨w, x, y, z, hw, hx, hy, hz, heq⟩
    refine ⟨(w, x, y, z), ?_, heq⟩
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_,
      Finset.mem_product.mpr ⟨?_, ?_⟩⟩⟩ <;>
      · rw [Finset.mem_range, Nat.lt_succ_iff]; assumption

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  sorry
