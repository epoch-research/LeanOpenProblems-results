import FormalConjectures.Util.ProblemImports

open Nat Finset Set

noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

noncomputable def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B

  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)

  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by sorry

theorem a306439_conjecture_1.disproof : ¬ (type_of% @a306439_conjecture_1) := sorry
