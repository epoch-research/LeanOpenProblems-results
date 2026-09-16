import Mathlib
open Real Int

noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    (2 ^ k + floor_val).pred.pred

lemma test : waring_g 4 = 19 := by
  sorry
