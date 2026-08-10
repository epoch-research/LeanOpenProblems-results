import Submission.ChebLB
import Submission.Combo
open Finset Real ChebLB
set_option maxRecDepth 8000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem log3_b : ((5493061/5000000 : ℝ) < Real.log 3) ∧ (Real.log 3 < (10986124/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/2 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 26
  rw [show (1 - (-1/2) : ℝ) = 3/2 by norm_num, Real.log_div (by norm_num) (by norm_num)] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> nlinarith [a, b, h1, h2]
theorem log5_b : ((8047189/5000000 : ℝ) < Real.log 5) ∧ (Real.log 5 < (16094380/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/4 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 14
  rw [show (1 - (-1/4) : ℝ) = 5/4 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> nlinarith [a, b, h1, h2]
theorem log7_b : ((194591/100000 : ℝ) < Real.log 7) ∧ (Real.log 7 < (19459102/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-1/7 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 11
  rw [show (1 - (-1/7) : ℝ) = 8/7 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> nlinarith [a, b, h1, h2]
theorem log11_b : ((2997369/1250000 : ℝ) < Real.log 11) ∧ (Real.log 11 < (23978954/10000000:ℝ)) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-3/8 : ℝ)) (by rw [abs_of_neg] <;> norm_num) 23
  rw [show (1 - (-3/8) : ℝ) = 11/8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      show (8:ℝ) = 2^3 by norm_num, Real.log_pow] at h
  norm_num [Finset.sum_range_succ, abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have a := Real.log_two_gt_d9; have b := Real.log_two_lt_d9
  norm_num at a b
  constructor <;> nlinarith [a, b, h1, h2]
theorem lk6 : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
  rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk10 : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
  rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk12 : Real.log (12:ℝ) = 2*Real.log 2 + Real.log 3 := by
  rw [show (12:ℝ) = (2^2)*3 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk14 : Real.log (14:ℝ) = Real.log 2 + Real.log 7 := by
  rw [show (14:ℝ) = 2*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk18 : Real.log (18:ℝ) = Real.log 2 + 2*Real.log 3 := by
  rw [show (18:ℝ) = 2*(3^2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk20 : Real.log (20:ℝ) = 2*Real.log 2 + Real.log 5 := by
  rw [show (20:ℝ) = (2^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk21 : Real.log (21:ℝ) = Real.log 3 + Real.log 7 := by
  rw [show (21:ℝ) = 3*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk30 : Real.log (30:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (30:ℝ) = 2*3*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk33 : Real.log (33:ℝ) = Real.log 3 + Real.log 11 := by
  rw [show (33:ℝ) = 3*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk35 : Real.log (35:ℝ) = Real.log 5 + Real.log 7 := by
  rw [show (35:ℝ) = 5*7 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk36 : Real.log (36:ℝ) = 2*Real.log 2 + 2*Real.log 3 := by
  rw [show (36:ℝ) = (2^2)*(3^2) by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk42 : Real.log (42:ℝ) = Real.log 2 + Real.log 3 + Real.log 7 := by
  rw [show (42:ℝ) = 2*3*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk44 : Real.log (44:ℝ) = 2*Real.log 2 + Real.log 11 := by
  rw [show (44:ℝ) = (2^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk45 : Real.log (45:ℝ) = 2*Real.log 3 + Real.log 5 := by
  rw [show (45:ℝ) = (3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk55 : Real.log (55:ℝ) = Real.log 5 + Real.log 11 := by
  rw [show (55:ℝ) = 5*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk60 : Real.log (60:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 := by
  rw [show (60:ℝ) = (2^2)*3*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk63 : Real.log (63:ℝ) = 2*Real.log 3 + Real.log 7 := by
  rw [show (63:ℝ) = (3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk66 : Real.log (66:ℝ) = Real.log 2 + Real.log 3 + Real.log 11 := by
  rw [show (66:ℝ) = 2*3*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk70 : Real.log (70:ℝ) = Real.log 2 + Real.log 5 + Real.log 7 := by
  rw [show (70:ℝ) = 2*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk77 : Real.log (77:ℝ) = Real.log 7 + Real.log 11 := by
  rw [show (77:ℝ) = 7*11 by norm_num, Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk84 : Real.log (84:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 7 := by
  rw [show (84:ℝ) = (2^2)*3*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk90 : Real.log (90:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 := by
  rw [show (90:ℝ) = 2*(3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk99 : Real.log (99:ℝ) = 2*Real.log 3 + Real.log 11 := by
  rw [show (99:ℝ) = (3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk105 : Real.log (105:ℝ) = Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (105:ℝ) = 3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk110 : Real.log (110:ℝ) = Real.log 2 + Real.log 5 + Real.log 11 := by
  rw [show (110:ℝ) = 2*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk126 : Real.log (126:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 7 := by
  rw [show (126:ℝ) = 2*(3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk132 : Real.log (132:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 11 := by
  rw [show (132:ℝ) = (2^2)*3*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk140 : Real.log (140:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 7 := by
  rw [show (140:ℝ) = (2^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk154 : Real.log (154:ℝ) = Real.log 2 + Real.log 7 + Real.log 11 := by
  rw [show (154:ℝ) = 2*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk165 : Real.log (165:ℝ) = Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (165:ℝ) = 3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk180 : Real.log (180:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 := by
  rw [show (180:ℝ) = (2^2)*(3^2)*5 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk198 : Real.log (198:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 11 := by
  rw [show (198:ℝ) = 2*(3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk210 : Real.log (210:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (210:ℝ) = 2*3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk220 : Real.log (220:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 11 := by
  rw [show (220:ℝ) = (2^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk231 : Real.log (231:ℝ) = Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (231:ℝ) = 3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk252 : Real.log (252:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 7 := by
  rw [show (252:ℝ) = (2^2)*(3^2)*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk308 : Real.log (308:ℝ) = 2*Real.log 2 + Real.log 7 + Real.log 11 := by
  rw [show (308:ℝ) = (2^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk315 : Real.log (315:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (315:ℝ) = (3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk330 : Real.log (330:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (330:ℝ) = 2*3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk385 : Real.log (385:ℝ) = Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (385:ℝ) = 5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk396 : Real.log (396:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 11 := by
  rw [show (396:ℝ) = (2^2)*(3^2)*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk420 : Real.log (420:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (420:ℝ) = (2^2)*3*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk462 : Real.log (462:ℝ) = Real.log 2 + Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (462:ℝ) = 2*3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk495 : Real.log (495:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (495:ℝ) = (3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk630 : Real.log (630:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (630:ℝ) = 2*(3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk660 : Real.log (660:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (660:ℝ) = (2^2)*3*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk693 : Real.log (693:ℝ) = 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (693:ℝ) = (3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk770 : Real.log (770:ℝ) = Real.log 2 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (770:ℝ) = 2*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk924 : Real.log (924:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (924:ℝ) = (2^2)*3*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk990 : Real.log (990:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (990:ℝ) = 2*(3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1155 : Real.log (1155:ℝ) = Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (1155:ℝ) = 3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk1260 : Real.log (1260:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 := by
  rw [show (1260:ℝ) = (2^2)*(3^2)*5*7 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk1386 : Real.log (1386:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (1386:ℝ) = 2*(3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1540 : Real.log (1540:ℝ) = 2*Real.log 2 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (1540:ℝ) = (2^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk1980 : Real.log (1980:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 11 := by
  rw [show (1980:ℝ) = (2^2)*(3^2)*5*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk2310 : Real.log (2310:ℝ) = Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (2310:ℝ) = 2*3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  try (push_cast; ring)
theorem lk2772 : Real.log (2772:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 7 + Real.log 11 := by
  rw [show (2772:ℝ) = (2^2)*(3^2)*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)
theorem lk3465 : Real.log (3465:ℝ) = 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (3465:ℝ) = (3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk4620 : Real.log (4620:ℝ) = 2*Real.log 2 + Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (4620:ℝ) = (2^2)*3*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk6930 : Real.log (6930:ℝ) = Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (6930:ℝ) = 2*(3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow]
  try (push_cast; ring)
theorem lk13860 : Real.log (13860:ℝ) = 2*Real.log 2 + 2*Real.log 3 + Real.log 5 + Real.log 7 + Real.log 11 := by
  rw [show (13860:ℝ) = (2^2)*(3^2)*5*7*11 by norm_num, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  try (push_cast; ring)

theorem Cval_eq : Cval Cmb.kset Cmb.acoef Cmb.Q = (4424186/12006225 : ℝ)*Real.log 2 + (4352207/16008300 : ℝ)*Real.log 3 + (2251801/19209960 : ℝ)*Real.log 5 + (119/2376 : ℝ)*Real.log 7 + (63233/1455300 : ℝ)*Real.log 11 := by
  unfold Cval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  push_cast
  simp only [Real.log_one]
  rw [lk6, lk10, lk12, lk14, lk18, lk20, lk21, lk30, lk33, lk35, lk36, lk42, lk44, lk45, lk55, lk60, lk63, lk66, lk70, lk77, lk84, lk90, lk99, lk105, lk110, lk126, lk132, lk140, lk154, lk165, lk180, lk198, lk210, lk220, lk231, lk252, lk308, lk315, lk330, lk385, lk396, lk420, lk462, lk495, lk630, lk660, lk693, lk770, lk924, lk990, lk1155, lk1260, lk1386, lk1540, lk1980, lk2310, lk2772, lk3465, lk4620, lk6930, lk13860]
  ring
theorem Kval_eq : Kval Cmb.kset Cmb.acoef Cmb.Q = (996299/13860 : ℝ) := by
  unfold Kval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  norm_num
theorem Lcval_eq : Lcval Cmb.kset Cmb.acoef Cmb.Q = (-99811/2310 : ℝ) + (197563/1980 : ℝ)*Real.log 2 + (628087/6930 : ℝ)*Real.log 3 + (118343/2772 : ℝ)*Real.log 5 + (650533/13860 : ℝ)*Real.log 7 + (579587/13860 : ℝ)*Real.log 11 + (348433/13860 : ℝ)*Real.log Real.pi := by
  unfold Lcval
  rw [show Cmb.kset = {1, 2, 3, 5, 6, 7, 10, 11, 12, 14, 18, 20, 21, 30, 33, 35, 36, 42, 44, 45, 55, 60, 63, 66, 70, 77, 84, 90, 99, 105, 110, 126, 132, 140, 154, 165, 180, 198, 210, 220, 231, 252, 308, 315, 330, 385, 396, 420, 462, 495, 630, 660, 693, 770, 924, 990, 1155, 1260, 1386, 1540, 1980, 2310, 2772, 3465, 4620, 6930, 13860} from rfl]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  simp only [Cmb.acoef, Cmb.Q]
  rw [show Real.log (2*Real.pi) = Real.log 2 + Real.log Real.pi from
      Real.log_mul (by norm_num) Real.pi_pos.ne']
  norm_num
  push_cast
  rw [lk6, lk10, lk12, lk14, lk18, lk20, lk21, lk30, lk33, lk35, lk36, lk42, lk44, lk45, lk55, lk60, lk63, lk66, lk70, lk77, lk84, lk90, lk99, lk105, lk110, lk126, lk132, lk140, lk154, lk165, lk180, lk198, lk210, lk220, lk231, lk252, lk308, lk315, lk330, lk385, lk396, lk420, lk462, lk495, lk630, lk660, lk693, lk770, lk924, lk990, lk1155, lk1260, lk1386, lk1540, lk1980, lk2310, lk2772, lk3465, lk4620, lk6930, lk13860]
  push_cast
  ring

theorem Cval_ge : ((7086731246918663/7503890625000000 : ℝ)) ≤ Cval Cmb.kset Cmb.acoef Cmb.Q := by
  rw [Cval_eq]
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  nlinarith [h2, log3_b.1, log5_b.1, log7_b.1, log11_b.1]
theorem Lcval_ge : ((57305525242160623/138600000000000 : ℝ)) ≤ Lcval Cmb.kset Cmb.acoef Cmb.Q := by
  rw [Lcval_eq]
  have h2 := Real.log_two_gt_d9
  have hpi : Real.log 3 ≤ Real.log Real.pi := Real.log_le_log (by norm_num) (le_of_lt Real.pi_gt_three)
  norm_num at h2
  nlinarith [h2, log3_b.1, log5_b.1, log7_b.1, log11_b.1, hpi]
