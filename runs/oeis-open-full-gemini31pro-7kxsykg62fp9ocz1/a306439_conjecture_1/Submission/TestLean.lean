import Mathlib

open Nat Finset Set

def P3_comp (k : ℕ) : ℕ := k * (3 * k + 1) / 2

def a_comp (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B

  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)

  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3_comp x + P3_comp y + 2 * P3_comp z + 3 * P3_comp w
  )).card

#eval (List.range 50).filter (fun n => a_comp n == 1)
