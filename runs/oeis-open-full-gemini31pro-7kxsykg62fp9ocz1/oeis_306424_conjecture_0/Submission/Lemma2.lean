import Mathlib

lemma region1 (b x : ℕ) (h1 : b ≥ 16) (h2 : x = 0) :
  let i := 3
  let B := b - i
  let k := b^2 + x
  let d2 := k / B^2
  let r2 := k % B^2
  let d1 := r2 / B
  let d0 := r2 % B
  d2 = 1 ∧ d1 ≠ 1 ∧ d0 ≠ 1 ∧ d1 ≠ d0 := by
  intro i B k d2 r2 d1 d0
  -- b^2 = (B+3)^2 = B^2 + 6B + 9
  sorry
