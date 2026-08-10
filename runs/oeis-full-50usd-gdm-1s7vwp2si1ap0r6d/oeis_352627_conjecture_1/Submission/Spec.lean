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

theorem a_pos_iff (n : ℕ) : 0 < a n ↔ ∃ x y z w : ℕ, x^2 + 2 * y^2 + z^4 + 4 * w^4 + z^2 * w^2 = n := by
  constructor
  · intro h
    rw [a] at h
    rcases card_pos.mp h with ⟨p, hp⟩
    rw [mem_filter] at hp
    rcases hp with ⟨_, hp2⟩
    use p.1, p.2.1, p.2.2.1, p.2.2.2
  · rintro ⟨x, y, z, w, h⟩
    rw [a, card_pos]
    -- We need to show the filtered set is nonempty by providing a witness
    have hx : x < sqrt n + 1 := by
      have h1 : x * x ≤ n := by
        calc x * x = x^2 := by ring
        _ ≤ n := by omega
      have h2 : x ≤ sqrt n := le_sqrt.mpr h1
      omega
    have hy : y < sqrt n + 1 := by
      have h1 : y * y ≤ n := by
        calc y * y = y^2 := by ring
        _ ≤ n := by omega
      have h2 : y ≤ sqrt n := le_sqrt.mpr h1
      omega
    have hz : z < sqrt n + 1 := by
      have h1 : (z^2) * (z^2) ≤ n := by
        calc (z^2) * (z^2) = z^4 := by ring
        _ ≤ n := by omega
      have h2 : z^2 ≤ sqrt n := le_sqrt.mpr h1
      have h4 : z * z ≤ n := by
        calc z * z = z^2 := by ring
        _ ≤ sqrt n := h2
        _ ≤ n := sqrt_le_self n
      have h5 : z ≤ sqrt n := le_sqrt.mpr h4
      omega
    have hw : w < sqrt n + 1 := by
      have h1 : (w^2) * (w^2) ≤ n := by
        calc (w^2) * (w^2) = w^4 := by ring
        _ ≤ n := by omega
      have h2 : w^2 ≤ sqrt n := le_sqrt.mpr h1
      have h4 : w * w ≤ n := by
        calc w * w = w^2 := by ring
        _ ≤ sqrt n := h2
        _ ≤ n := sqrt_le_self n
      have h5 : w ≤ sqrt n := le_sqrt.mpr h4
      omega
    -- Let's construct the witness
    use (x, y, z, w)
    rw [mem_filter]
    constructor
    · -- Show p ∈ S_quadruples
      apply mem_product.mpr
      constructor
      · rw [mem_range]; exact hx
      · apply mem_product.mpr
        constructor
        · rw [mem_range]; exact hy
        · apply mem_product.mpr
          constructor
          · rw [mem_range]; exact hz
          · rw [mem_range]; exact hw
    · -- Show equation holds for p
      exact h

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  sorry

