import FormalConjectures.Util.ProblemImports
open Nat

lemma div2_lt_of_add_two_le {s y : ℕ} (h : s + 2 ≤ y) : s/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega

lemma div2_lt_of_boundary {x y : ℕ} (hpos : 0 < x) (h : x + 1 + x/2 ≤ y) : x/2 < y/2 := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega

lemma div2_div2_le_half_add {x y : ℕ} (h : x/2 ≤ y) : (x/2)/2 ≤ (y + 0)/2 := by
  apply Nat.div_le_div_right
  simpa using h
