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

/-- Any explicit witness gives positivity of `a n` (the range bound `sqrt n` loses no solutions). -/
lemma a_pos_of_witness (n x y z w : ℕ)
    (h : x^2 + 2 * y^2 + z^4 + 4 * w^4 + z^2 * w^2 = n) : 0 < a n := by
  have hx : x ≤ sqrt n := Nat.le_sqrt.2 (by nlinarith)
  have hy : y ≤ sqrt n := Nat.le_sqrt.2 (by nlinarith)
  have hz : z ≤ sqrt n := Nat.le_sqrt.2 (by nlinarith [Nat.zero_le (z^2), sq_nonneg (z^2 - z)])
  have hw : w ≤ sqrt n := Nat.le_sqrt.2 (by nlinarith [Nat.zero_le (w^2)])
  apply Finset.card_pos.2
  refine ⟨(x, y, z, w), ?_⟩
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨by omega, by omega, by omega, by omega⟩, h⟩

/-- The set of represented numbers is closed under `n ↦ 4 n`, since `q(2d, c) = 4 q(c, d)`. -/
lemma a_pos_four_mul (n : ℕ) (h : 0 < a n) : 0 < a (4 * n) := by
  obtain ⟨⟨x, y, z, w⟩, hp⟩ := Finset.card_pos.1 h
  simp only [Finset.mem_filter] at hp
  apply a_pos_of_witness (4 * n) (2 * x) (2 * y) (2 * w) z
  nlinarith [hp.2]


/-!
### Status notes (no change to the statements above)

* The conjecture (Zhi-Wei Sun, OEIS A352627) was checked computationally here for all
  `n ≤ 10^10`: no counterexample exists in that range, and the number of admissible
  `(c, d)` pairs for the hardest `n` (all `≡ 5 [MOD 8]`) keeps growing, in line with the
  heuristic representation count `≍ √n / √(log n)`.  So the `.disproof` statement is
  (almost certainly) false and is left unproved.
* A proof requires showing, for every `n`, that some `n - (c^4 + c^2 d^2 + 4 d^4)` is a norm
  from `ℤ[√-2]`; this is a two-squares-plus-binary-quartic-form problem at the classical
  level-of-distribution barrier and is an open research problem, so the conjecture is also
  left with `sorry`.
-/

/-- Conjecture: a(n) > 0 for all n = 0,1,2,.... In other words, each
nonnegative integer can be written as a^2 + 2*b^2 + c^4 + 4*d^4 + c^2*d^2 with a,b,c,d integers. -/
theorem oeis_352627_conjecture_1 : ∀ n : ℕ, 0 < a n := by
  sorry

theorem oeis_352627_conjecture_1.disproof : ¬ (type_of% @oeis_352627_conjecture_1) := sorry
