import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 800000


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

example (n : ℕ) (h : n ≤ 60) :
    (a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ)) := by
  interval_cases n <;> unfold a P3 <;> native_decide

example (n : ℕ) (h₁ : 5 < n) (h₂ : n ≤ 60) : a n > 0 := by
  interval_cases n <;> unfold a P3 <;> native_decide
