import FormalConjectures.Util.ProblemImports

open Nat
open Real

/--
A000040: The prime numbers.
The $n$-th prime number $p_n$, where $p_1 = 2$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | (n' + 1) => nth Nat.Prime n'

theorem oeis_40_conjecture_5_n1 :
  Real.log (Real.log ((a 2).cast : ℝ)) - Real.log (Real.log ((a 1).cast : ℝ)) < 1 := by
  have ha2 : a 2 = 3 := by
    change nth Nat.Prime 1 = 3
    exact nth_prime_one_eq_three
  have ha1 : a 1 = 2 := by
    change nth Nat.Prime 0 = 2
    exact nth_prime_zero_eq_two
  rw [ha2, ha1]
  simp only [Nat.cast_ofNat]
  have h_exp1 : (27182818283 / 10000000000 : ℝ) < Real.exp 1 := by
    have h1 := Real.exp_one_gt_d9
    have h2 : (27182818283 / 10000000000 : ℝ) = 2.7182818283 := by norm_num
    rwa [h2]
  have h_log2 : (6931 / 10000 : ℝ) < Real.log 2 := by
    have h1 := Real.log_two_gt_d9
    have h2 : (6931 / 10000 : ℝ) < 0.6931471803 := by norm_num
    exact lt_trans h2 h1
  have h_log2_pos : 0 < Real.log 2 := by linarith
  have h_pos : 0 < 3 / Real.exp 1 := by positivity
  have h_le := Real.log_le_sub_one_of_pos h_pos
  have h_log_div : Real.log (3 / Real.exp 1) = Real.log 3 - 1 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_exp]
  rw [h_log_div] at h_le
  have h_log3_le : Real.log 3 ≤ 3 / Real.exp 1 := by linarith
  have h_div_lt : 3 / Real.exp 1 < 11037 / 10000 := by
    rw [div_lt_iff₀ (by positivity)]
    have : 3 < (11037 / 10000 : ℝ) * (27182818283 / 10000000000 : ℝ) := by norm_num
    linarith
  have h_log3 : Real.log 3 < 11037 / 10000 := lt_of_le_of_lt h_log3_le h_div_lt
  have h_ratio : Real.log 3 / Real.log 2 < 11037 / 10000 / (6931 / 10000) := by
    have h1 : Real.log 3 / Real.log 2 < (11037 / 10000) / Real.log 2 := by
      exact div_lt_div_of_pos_right h_log3 h_log2_pos
    have h2 : (11037 / 10000) / Real.log 2 < (11037 / 10000) / (6931 / 10000 : ℝ) := by
      exact div_lt_div_of_pos_left (by norm_num) (by norm_num) h_log2
    exact lt_trans h1 h2
  have h_exp_bound : (11037 / 10000 : ℝ) / (6931 / 10000 : ℝ) < Real.exp 1 := by
    have : (11037 / 10000 : ℝ) / (6931 / 10000 : ℝ) < (27182818283 / 10000000000 : ℝ) := by norm_num
    linarith
  have h_lt : Real.log 3 / Real.log 2 < Real.exp 1 := lt_trans h_ratio h_exp_bound
  have h_ratio_pos : 0 < Real.log 3 / Real.log 2 := div_pos (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 3)]) h_log2_pos
  have h_log_lt : Real.log (Real.log 3 / Real.log 2) < 1 := by
    rwa [Real.log_lt_iff_lt_exp h_ratio_pos]
  rw [Real.log_div (by linarith [Real.log_pos (by norm_num : (1:ℝ) < 3)]) (by linarith)] at h_log_lt
  exact h_log_lt

theorem oeis_40_conjecture_5_n2 :
  Real.log (Real.log ((a 3).cast : ℝ)) - Real.log (Real.log ((a 2).cast : ℝ)) < 1 / 2 := by
  have ha3 : a 3 = 5 := by
    change nth Nat.Prime 2 = 5
    exact nth_prime_two_eq_five
  have ha2 : a 2 = 3 := by
    change nth Nat.Prime 1 = 3
    exact nth_prime_one_eq_three
  rw [ha3, ha2]
  simp only [Nat.cast_ofNat]
  have h_log3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h_log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 5 / Real.log 3 := div_pos h_log5_pos h_log3_pos
  have h_sub : Real.log (Real.log 5) - Real.log (Real.log 3) = Real.log (Real.log 5 / Real.log 3) := by
    rw [Real.log_div (ne_of_gt h_log5_pos) (ne_of_gt h_log3_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 5 / Real.log 3 - 1 = (Real.log 5 - Real.log 3) / Real.log 3 := by
    have h_ne : Real.log 3 ≠ 0 := ne_of_gt h_log3_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 5 - Real.log 3) / Real.log 3 < 1 / 2 := by
    rw [div_lt_iff₀ h_log3_pos]
    have h_log5_eq : 2 * Real.log 5 = Real.log 25 := by
      have : (2 : ℝ) * Real.log 5 = Real.log (5 ^ (2 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 2]
      rw [this]
      norm_num
    have h_log3_eq : 3 * Real.log 3 = Real.log 27 := by
      have : (3 : ℝ) * Real.log 3 = Real.log (3 ^ (3 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 3]
      rw [this]
      norm_num
    have h_log_mono : Real.log 25 < Real.log 27 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n3 :
  Real.log (Real.log ((a 4).cast : ℝ)) - Real.log (Real.log ((a 3).cast : ℝ)) < 1 / 3 := by
  have ha4 : a 4 = 7 := by
    change nth Nat.Prime 3 = 7
    exact nth_prime_three_eq_seven
  have ha3 : a 3 = 5 := by
    change nth Nat.Prime 2 = 5
    exact nth_prime_two_eq_five
  rw [ha4, ha3]
  simp only [Nat.cast_ofNat]
  have h_log5_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h_log7_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 7 / Real.log 5 := div_pos h_log7_pos h_log5_pos
  have h_sub : Real.log (Real.log 7) - Real.log (Real.log 5) = Real.log (Real.log 7 / Real.log 5) := by
    rw [Real.log_div (ne_of_gt h_log7_pos) (ne_of_gt h_log5_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 7 / Real.log 5 - 1 = (Real.log 7 - Real.log 5) / Real.log 5 := by
    have h_ne : Real.log 5 ≠ 0 := ne_of_gt h_log5_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 7 - Real.log 5) / Real.log 5 < 1 / 3 := by
    rw [div_lt_iff₀ h_log5_pos]
    have h_log7_eq : 3 * Real.log 7 = Real.log 343 := by
      have : (3 : ℝ) * Real.log 7 = Real.log (7 ^ (3 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 3]
      rw [this]
      norm_num
    have h_log5_eq : 4 * Real.log 5 = Real.log 625 := by
      have : (4 : ℝ) * Real.log 5 = Real.log (5 ^ (4 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 4]
      rw [this]
      norm_num
    have h_log_mono : Real.log 343 < Real.log 625 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n4 :
  Real.log (Real.log ((a 5).cast : ℝ)) - Real.log (Real.log ((a 4).cast : ℝ)) < 1 / 4 := by
  have ha5 : a 5 = 11 := by
    change nth Nat.Prime 4 = 11
    exact nth_prime_four_eq_eleven
  have ha4 : a 4 = 7 := by
    change nth Nat.Prime 3 = 7
    exact nth_prime_three_eq_seven
  rw [ha5, ha4]
  simp only [Nat.cast_ofNat]
  have h_log7_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h_log11_pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 11 / Real.log 7 := div_pos h_log11_pos h_log7_pos
  have h_sub : Real.log (Real.log 11) - Real.log (Real.log 7) = Real.log (Real.log 11 / Real.log 7) := by
    rw [Real.log_div (ne_of_gt h_log11_pos) (ne_of_gt h_log7_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 11 / Real.log 7 - 1 = (Real.log 11 - Real.log 7) / Real.log 7 := by
    have h_ne : Real.log 7 ≠ 0 := ne_of_gt h_log7_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 11 - Real.log 7) / Real.log 7 < 1 / 4 := by
    rw [div_lt_iff₀ h_log7_pos]
    have h_log11_eq : 4 * Real.log 11 = Real.log 14641 := by
      have : (4 : ℝ) * Real.log 11 = Real.log (11 ^ (4 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 4]
      rw [this]
      norm_num
    have h_log7_eq : 5 * Real.log 7 = Real.log 16807 := by
      have : (5 : ℝ) * Real.log 7 = Real.log (7 ^ (5 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 5]
      rw [this]
      norm_num
    have h_log_mono : Real.log 14641 < Real.log 16807 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n5 :
  Real.log (Real.log ((a 6).cast : ℝ)) - Real.log (Real.log ((a 5).cast : ℝ)) < 1 / 5 := by
  have ha6 : a 6 = 13 := by
    change nth Nat.Prime 5 = 13
    have h_count : count Nat.Prime 13 = 5 := rfl
    have h_prime : Nat.Prime 13 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha5 : a 5 = 11 := by
    change nth Nat.Prime 4 = 11
    exact nth_prime_four_eq_eleven
  rw [ha6, ha5]
  simp only [Nat.cast_ofNat]
  have h_log11_pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
  have h_log13_pos : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 13 / Real.log 11 := div_pos h_log13_pos h_log11_pos
  have h_sub : Real.log (Real.log 13) - Real.log (Real.log 11) = Real.log (Real.log 13 / Real.log 11) := by
    rw [Real.log_div (ne_of_gt h_log13_pos) (ne_of_gt h_log11_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 13 / Real.log 11 - 1 = (Real.log 13 - Real.log 11) / Real.log 11 := by
    have h_ne : Real.log 11 ≠ 0 := ne_of_gt h_log11_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 13 - Real.log 11) / Real.log 11 < 1 / 5 := by
    rw [div_lt_iff₀ h_log11_pos]
    have h_log13_eq : 5 * Real.log 13 = Real.log 371293 := by
      have : (5 : ℝ) * Real.log 13 = Real.log (13 ^ (5 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 5]
      rw [this]
      norm_num
    have h_log11_eq : 6 * Real.log 11 = Real.log 1771561 := by
      have : (6 : ℝ) * Real.log 11 = Real.log (11 ^ (6 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 6]
      rw [this]
      norm_num
    have h_log_mono : Real.log 371293 < Real.log 1771561 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n6 :
  Real.log (Real.log ((a 7).cast : ℝ)) - Real.log (Real.log ((a 6).cast : ℝ)) < 1 / 6 := by
  have ha7 : a 7 = 17 := by
    change nth Nat.Prime 6 = 17
    have h_count : count Nat.Prime 17 = 6 := rfl
    have h_prime : Nat.Prime 17 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha6 : a 6 = 13 := by
    change nth Nat.Prime 5 = 13
    have h_count : count Nat.Prime 13 = 5 := rfl
    have h_prime : Nat.Prime 13 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  rw [ha7, ha6]
  simp only [Nat.cast_ofNat]
  have h_log13_pos : 0 < Real.log 13 := Real.log_pos (by norm_num)
  have h_log17_pos : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 17 / Real.log 13 := div_pos h_log17_pos h_log13_pos
  have h_sub : Real.log (Real.log 17) - Real.log (Real.log 13) = Real.log (Real.log 17 / Real.log 13) := by
    rw [Real.log_div (ne_of_gt h_log17_pos) (ne_of_gt h_log13_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 17 / Real.log 13 - 1 = (Real.log 17 - Real.log 13) / Real.log 13 := by
    have h_ne : Real.log 13 ≠ 0 := ne_of_gt h_log13_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 17 - Real.log 13) / Real.log 13 < 1 / 6 := by
    rw [div_lt_iff₀ h_log13_pos]
    have h_log17_eq : 6 * Real.log 17 = Real.log 24137569 := by
      have : (6 : ℝ) * Real.log 17 = Real.log (17 ^ (6 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 6]
      rw [this]
      norm_num
    have h_log13_eq : 7 * Real.log 13 = Real.log 62748517 := by
      have : (7 : ℝ) * Real.log 13 = Real.log (13 ^ (7 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 7]
      rw [this]
      norm_num
    have h_log_mono : Real.log 24137569 < Real.log 62748517 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt


theorem oeis_40_conjecture_5_n7 :
  Real.log (Real.log ((a 8).cast : ℝ)) - Real.log (Real.log ((a 7).cast : ℝ)) < 1 / 7 := by
  have ha8 : a 8 = 19 := by
    change nth Nat.Prime 7 = 19
    have h_count : count Nat.Prime 19 = 7 := rfl
    have h_prime : Nat.Prime 19 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha7 : a 7 = 17 := by
    change nth Nat.Prime 6 = 17
    have h_count : count Nat.Prime 17 = 6 := rfl
    have h_prime : Nat.Prime 17 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  rw [ha8, ha7]
  simp only [Nat.cast_ofNat]
  have h_log17_pos : 0 < Real.log 17 := Real.log_pos (by norm_num)
  have h_log19_pos : 0 < Real.log 19 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 19 / Real.log 17 := div_pos h_log19_pos h_log17_pos
  have h_sub : Real.log (Real.log 19) - Real.log (Real.log 17) = Real.log (Real.log 19 / Real.log 17) := by
    rw [Real.log_div (ne_of_gt h_log19_pos) (ne_of_gt h_log17_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 19 / Real.log 17 - 1 = (Real.log 19 - Real.log 17) / Real.log 17 := by
    have h_ne : Real.log 17 ≠ 0 := ne_of_gt h_log17_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 19 - Real.log 17) / Real.log 17 < 1 / 7 := by
    rw [div_lt_iff₀ h_log17_pos]
    have h_log19_eq : 7 * Real.log 19 = Real.log 893871739 := by
      have : (7 : ℝ) * Real.log 19 = Real.log (19 ^ (7 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 7]
      rw [this]
      norm_num
    have h_log17_eq : 8 * Real.log 17 = Real.log 6975757441 := by
      have : (8 : ℝ) * Real.log 17 = Real.log (17 ^ (8 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 8]
      rw [this]
      norm_num
    have h_log_mono : Real.log 893871739 < Real.log 6975757441 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n8 :
  Real.log (Real.log ((a 9).cast : ℝ)) - Real.log (Real.log ((a 8).cast : ℝ)) < 1 / 8 := by
  have ha9 : a 9 = 23 := by
    change nth Nat.Prime 8 = 23
    have h_count : count Nat.Prime 23 = 8 := rfl
    have h_prime : Nat.Prime 23 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha8 : a 8 = 19 := by
    change nth Nat.Prime 7 = 19
    have h_count : count Nat.Prime 19 = 7 := rfl
    have h_prime : Nat.Prime 19 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  rw [ha9, ha8]
  simp only [Nat.cast_ofNat]
  have h_log19_pos : 0 < Real.log 19 := Real.log_pos (by norm_num)
  have h_log23_pos : 0 < Real.log 23 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 23 / Real.log 19 := div_pos h_log23_pos h_log19_pos
  have h_sub : Real.log (Real.log 23) - Real.log (Real.log 19) = Real.log (Real.log 23 / Real.log 19) := by
    rw [Real.log_div (ne_of_gt h_log23_pos) (ne_of_gt h_log19_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 23 / Real.log 19 - 1 = (Real.log 23 - Real.log 19) / Real.log 19 := by
    have h_ne : Real.log 19 ≠ 0 := ne_of_gt h_log19_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 23 - Real.log 19) / Real.log 19 < 1 / 8 := by
    rw [div_lt_iff₀ h_log19_pos]
    have h_log23_eq : 8 * Real.log 23 = Real.log 78310985281 := by
      have : (8 : ℝ) * Real.log 23 = Real.log (23 ^ (8 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 8]
      rw [this]
      norm_num
    have h_log19_eq : 9 * Real.log 19 = Real.log 322687697779 := by
      have : (9 : ℝ) * Real.log 19 = Real.log (19 ^ (9 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 9]
      rw [this]
      norm_num
    have h_log_mono : Real.log 78310985281 < Real.log 322687697779 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt


theorem oeis_40_conjecture_5_n9 :
  Real.log (Real.log ((a 10).cast : ℝ)) - Real.log (Real.log ((a 9).cast : ℝ)) < 1 / 9 := by
  have ha10 : a 10 = 29 := by
    change nth Nat.Prime 9 = 29
    have h_count : count Nat.Prime 29 = 9 := rfl
    have h_prime : Nat.Prime 29 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha9 : a 9 = 23 := by
    change nth Nat.Prime 8 = 23
    have h_count : count Nat.Prime 23 = 8 := rfl
    have h_prime : Nat.Prime 23 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  rw [ha10, ha9]
  simp only [Nat.cast_ofNat]
  have h_log23_pos : 0 < Real.log 23 := Real.log_pos (by norm_num)
  have h_log29_pos : 0 < Real.log 29 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 29 / Real.log 23 := div_pos h_log29_pos h_log23_pos
  have h_sub : Real.log (Real.log 29) - Real.log (Real.log 23) = Real.log (Real.log 29 / Real.log 23) := by
    rw [Real.log_div (ne_of_gt h_log29_pos) (ne_of_gt h_log23_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 29 / Real.log 23 - 1 = (Real.log 29 - Real.log 23) / Real.log 23 := by
    have h_ne : Real.log 23 ≠ 0 := ne_of_gt h_log23_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 29 - Real.log 23) / Real.log 23 < 1 / 9 := by
    rw [div_lt_iff₀ h_log23_pos]
    have h_log29_eq : 9 * Real.log 29 = Real.log 14507145975869 := by
      have : (9 : ℝ) * Real.log 29 = Real.log (29 ^ (9 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 9]
      rw [this]
      norm_num
    have h_log23_eq : 10 * Real.log 23 = Real.log 41426511213649 := by
      have : (10 : ℝ) * Real.log 23 = Real.log (23 ^ (10 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 10]
      rw [this]
      norm_num
    have h_log_mono : Real.log 14507145975869 < Real.log 41426511213649 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt

theorem oeis_40_conjecture_5_n10 :
  Real.log (Real.log ((a 11).cast : ℝ)) - Real.log (Real.log ((a 10).cast : ℝ)) < 1 / 10 := by
  have ha11 : a 11 = 31 := by
    change nth Nat.Prime 10 = 31
    have h_count : count Nat.Prime 31 = 10 := rfl
    have h_prime : Nat.Prime 31 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  have ha10 : a 10 = 29 := by
    change nth Nat.Prime 9 = 29
    have h_count : count Nat.Prime 29 = 9 := rfl
    have h_prime : Nat.Prime 29 := by decide
    have h_nth := nth_count h_prime
    rwa [h_count] at h_nth
  rw [ha11, ha10]
  simp only [Nat.cast_ofNat]
  have h_log29_pos : 0 < Real.log 29 := Real.log_pos (by norm_num)
  have h_log31_pos : 0 < Real.log 31 := Real.log_pos (by norm_num)
  have h_ratio_pos : 0 < Real.log 31 / Real.log 29 := div_pos h_log31_pos h_log29_pos
  have h_sub : Real.log (Real.log 31) - Real.log (Real.log 29) = Real.log (Real.log 31 / Real.log 29) := by
    rw [Real.log_div (ne_of_gt h_log31_pos) (ne_of_gt h_log29_pos)]
  rw [h_sub]
  have h1 := Real.log_le_sub_one_of_pos h_ratio_pos
  have h2 : Real.log 31 / Real.log 29 - 1 = (Real.log 31 - Real.log 29) / Real.log 29 := by
    have h_ne : Real.log 29 ≠ 0 := ne_of_gt h_log29_pos
    rw [sub_div, div_self h_ne]
  rw [h2] at h1
  have h_lt : (Real.log 31 - Real.log 29) / Real.log 29 < 1 / 10 := by
    rw [div_lt_iff₀ h_log29_pos]
    have h_log31_eq : 10 * Real.log 31 = Real.log 819628286980801 := by
      have : (10 : ℝ) * Real.log 31 = Real.log (31 ^ (10 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 10]
      rw [this]
      norm_num
    have h_log29_eq : 11 * Real.log 29 = Real.log 12200509765705829 := by
      have : (11 : ℝ) * Real.log 29 = Real.log (29 ^ (11 : ℝ)) := by
        rw [Real.log_rpow (by norm_num) 11]
      rw [this]
      norm_num
    have h_log_mono : Real.log 819628286980801 < Real.log 12200509765705829 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact lt_of_le_of_lt h1 h_lt


/--
A000040 Conjecture: log log a(n+1) - log log a(n) < 1/n. - _Thomas Ordowski_, Feb 17 2023
-/
theorem oeis_40_conjecture_5 (n : ℕ) (hn : 0 < n) :
  Real.log (Real.log ((a (n + 1)).cast : ℝ)) - Real.log (Real.log ((a n).cast : ℝ)) < 1 / (n.cast : ℝ) := by
  rcases Nat.exists_eq_succ_of_ne_zero (_root_.ne_of_gt hn) with ⟨m, rfl⟩
  rcases m with _ | m'
  · have h_eq1 : a (succ 0 + 1) = a 2 := rfl
    have h_eq2 : a (succ 0) = a 1 := rfl
    have h_eq3 : ((succ 0).cast : ℝ) = 1 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    have h_div : 1 / (1 : ℝ) = 1 := by norm_num
    rw [h_div]
    exact oeis_40_conjecture_5_n1
  rcases m' with _ | m''
  · have h_eq1 : a (succ 1 + 1) = a 3 := rfl
    have h_eq2 : a (succ 1) = a 2 := rfl
    have h_eq3 : ((succ 1).cast : ℝ) = 2 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n2
  rcases m'' with _ | m'''
  · have h_eq1 : a (succ 2 + 1) = a 4 := rfl
    have h_eq2 : a (succ 2) = a 3 := rfl
    have h_eq3 : ((succ 2).cast : ℝ) = 3 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n3
  rcases m''' with _ | m''''
  · have h_eq1 : a (succ 3 + 1) = a 5 := rfl
    have h_eq2 : a (succ 3) = a 4 := rfl
    have h_eq3 : ((succ 3).cast : ℝ) = 4 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n4
  rcases m'''' with _ | m'''''
  · have h_eq1 : a (succ 4 + 1) = a 6 := rfl
    have h_eq2 : a (succ 4) = a 5 := rfl
    have h_eq3 : ((succ 4).cast : ℝ) = 5 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n5
  rcases m''''' with _ | m''''''
  · have h_eq1 : a (succ 5 + 1) = a 7 := rfl
    have h_eq2 : a (succ 5) = a 6 := rfl
    have h_eq3 : ((succ 5).cast : ℝ) = 6 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n6
  rcases m'''''' with _ | m'''''''
  · have h_eq1 : a (succ 6 + 1) = a 8 := rfl
    have h_eq2 : a (succ 6) = a 7 := rfl
    have h_eq3 : ((succ 6).cast : ℝ) = 7 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n7
  rcases m''''''' with _ | m''''''''
  · have h_eq1 : a (succ 7 + 1) = a 9 := rfl
    have h_eq2 : a (succ 7) = a 8 := rfl
    have h_eq3 : ((succ 7).cast : ℝ) = 8 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n8
  rcases m'''''''' with _ | m'''''''''
  · have h_eq1 : a (succ 8 + 1) = a 10 := rfl
    have h_eq2 : a (succ 8) = a 9 := rfl
    have h_eq3 : ((succ 8).cast : ℝ) = 9 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n9
  rcases m''''''''' with _ | m''''''''''
  · have h_eq1 : a (succ 9 + 1) = a 11 := rfl
    have h_eq2 : a (succ 9) = a 10 := rfl
    have h_eq3 : ((succ 9).cast : ℝ) = 10 := by simp
    rw [h_eq1, h_eq2, h_eq3]
    exact oeis_40_conjecture_5_n10
  sorry
