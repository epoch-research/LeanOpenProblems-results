import FormalConjectures.Util.ProblemImports

open Nat Finset Set

noncomputable def a (n : ℕ) : ℕ :=
  let R := range (n + 1)
  let search_space := (R.product R).product R
  let S1 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + z^2 = n
  let S5 : Finset ((ℕ × ℕ) × ℕ) :=
    search_space.filter fun p =>
      let x := p.fst.fst; let y := p.fst.snd; let z := p.snd;
      x^3 + 2 * y^2 + 5 * z^2 = n ∧ z ≠ 0
  S1.card + S5.card

theorem oeis_a275150_conjecture_2_sun :
  ∀ (a b c i j k : ℕ),
    0 < a → 0 < b → 0 < c →
    1 < i → 1 < j → 1 < k →
  (let S : Set ℕ := {n | ∃ x y z : ℕ, n = a * x^i + b * y^j + c * z^k}
   Set.Infinite {n : ℕ+ | (n : ℕ) ∉ S}) := by sorry

theorem oeis_a275150_conjecture_2_sun.disproof : ¬ (type_of% @oeis_a275150_conjecture_2_sun) := by
  sorry
