import Submission.Spec
open Nat Finset

def A369462_comp (n : ℕ) : ℕ :=
  if 1 ≤ n then
    let N : ℕ := 12 * n - 1
    let B := N
    let search_range := range (B + 1)
    let search_space := search_range.product (search_range.product search_range)

    (search_space.filter (fun t : ℕ × ℕ × ℕ =>
      let p := t.fst
      let q := t.snd.fst
      let r := t.snd.snd
      p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ r.Prime ∧ r ≠ 2 ∧
      p ≤ q ∧ q ≤ r ∧ p * q + p * r + q * r = N
    )).card
  else
    0

#eval A369462_comp 6
