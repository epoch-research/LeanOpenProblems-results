import Mathlib

lemma helper1 (b x : ℕ) (h1 : b ≥ 13) (h2 : x ≤ 2 * b) :
  ∃ i : ℕ, i ≤ 4 ∧ 
  (let B := b - i
   let rem := x + 2 * b * i
   let d1 := (rem - i * i) / B
   let d0 := (rem - i * i) % B
   d1 ≠ 1 ∧ d0 ≠ 1 ∧ d1 ≠ d0) := by
  sorry
