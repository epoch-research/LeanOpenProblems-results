import Mathlib

open Real
open Int

noncomputable def waring_g (k : ℕ) : ℕ :=
  if k < 2 then 0
  else
    let k_re : ℝ := k
    let three_half_pow_k_real : ℝ := (3 / 2) ^ k_re
    let floor_val : ℕ := Int.toNat (floor three_half_pow_k_real)
    (2 ^ k + floor_val).pred.pred

lemma waring_g_3_eq_7 : waring_g 3 = 7 := by
  dsimp [waring_g]
  norm_num

lemma waring_g_3_eq_9 : waring_g 3 = 9 := by
  dsimp [waring_g]
  norm_num
