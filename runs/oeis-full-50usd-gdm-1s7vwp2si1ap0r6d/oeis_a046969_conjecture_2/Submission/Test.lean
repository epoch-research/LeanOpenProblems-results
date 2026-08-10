import FormalConjectures.Util.ProblemImports
open Rat Nat Finset

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let m := 2 * n
    let k := m * (m - 1)
    (bernoulli m / (k : ℚ)).den

lemma bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 6]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [this]
  have h1 : Nat.choose 6 2 = 15 := by decide
  have h2 : Nat.choose 6 4 = 15 := by decide
  rw [h1, h2]
  norm_num

lemma bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_six

lemma bernoulli_eight : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 8]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7]
  have c1 : Nat.choose 8 2 = 28 := by decide
  have c2 : Nat.choose 8 4 = 70 := by decide
  have c3 : Nat.choose 8 6 = 28 := by decide
  rw [c1, c2, c3]
  norm_num

lemma bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_eight

lemma bernoulli_ten : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 10]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h8 : bernoulli' 8 = -1 / 30 := bernoulli'_eight
  have h9 : bernoulli' 9 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7, h8, h9]
  have c1 : Nat.choose 10 2 = 45 := by decide
  have c2 : Nat.choose 10 4 = 210 := by decide
  have c3 : Nat.choose 10 6 = 210 := by decide
  have c4 : Nat.choose 10 8 = 45 := by decide
  rw [c1, c2, c3, c4]
  norm_num

lemma bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_ten

lemma bernoulli_twelve : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 12]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h8 : bernoulli' 8 = -1 / 30 := bernoulli'_eight
  have h9 : bernoulli' 9 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h10 : bernoulli' 10 = 5 / 66 := bernoulli'_ten
  have h11 : bernoulli' 11 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7, h8, h9, h10, h11]
  have c1 : Nat.choose 12 2 = 66 := by decide
  have c2 : Nat.choose 12 4 = 495 := by decide
  have c3 : Nat.choose 12 6 = 924 := by decide
  have c4 : Nat.choose 12 8 = 495 := by decide
  have c5 : Nat.choose 12 10 = 66 := by decide
  rw [c1, c2, c3, c4, c5]
  norm_num

lemma bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_twelve

lemma bernoulli_fourteen : bernoulli 14 = 7 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 14]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h8 : bernoulli' 8 = -1 / 30 := bernoulli'_eight
  have h9 : bernoulli' 9 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h10 : bernoulli' 10 = 5 / 66 := bernoulli'_ten
  have h11 : bernoulli' 11 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h12 : bernoulli' 12 = -691 / 2730 := bernoulli'_twelve
  have h13 : bernoulli' 13 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7, h8, h9, h10, h11, h12, h13]
  have c1 : Nat.choose 14 2 = 91 := by decide
  have c2 : Nat.choose 14 4 = 1001 := by decide
  have c3 : Nat.choose 14 6 = 3003 := by decide
  have c4 : Nat.choose 14 8 = 3003 := by decide
  have c5 : Nat.choose 14 10 = 1001 := by decide
  have c6 : Nat.choose 14 12 = 91 := by decide
  rw [c1, c2, c3, c4, c5, c6]
  norm_num

lemma bernoulli'_fourteen : bernoulli' 14 = 7 / 6 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_fourteen

lemma bernoulli_sixteen : bernoulli 16 = -3617 / 510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 16]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h8 : bernoulli' 8 = -1 / 30 := bernoulli'_eight
  have h9 : bernoulli' 9 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h10 : bernoulli' 10 = 5 / 66 := bernoulli'_ten
  have h11 : bernoulli' 11 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h12 : bernoulli' 12 = -691 / 2730 := bernoulli'_twelve
  have h13 : bernoulli' 13 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h14 : bernoulli' 14 = 7 / 6 := bernoulli'_fourteen
  have h15 : bernoulli' 15 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  have c1 : Nat.choose 16 2 = 120 := by decide
  have c2 : Nat.choose 16 4 = 1820 := by decide
  have c3 : Nat.choose 16 6 = 8008 := by decide
  have c4 : Nat.choose 16 8 = 12870 := by decide
  have c5 : Nat.choose 16 10 = 8008 := by decide
  have c6 : Nat.choose 16 12 = 1820 := by decide
  have c7 : Nat.choose 16 14 = 120 := by decide
  rw [c1, c2, c3, c4, c5, c6, c7]
  norm_num

lemma bernoulli'_sixteen : bernoulli' 16 = -3617 / 510 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_sixteen

lemma bernoulli_eighteen : bernoulli 18 = 43867 / 798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  rw [bernoulli'_def 18]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four]
  have h5 : bernoulli' 5 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h6 : bernoulli' 6 = 1 / 42 := bernoulli'_six
  have h7 : bernoulli' 7 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h8 : bernoulli' 8 = -1 / 30 := bernoulli'_eight
  have h9 : bernoulli' 9 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h10 : bernoulli' 10 = 5 / 66 := bernoulli'_ten
  have h11 : bernoulli' 11 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h12 : bernoulli' 12 = -691 / 2730 := bernoulli'_twelve
  have h13 : bernoulli' 13 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h14 : bernoulli' 14 = 7 / 6 := bernoulli'_fourteen
  have h15 : bernoulli' 15 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  have h16 : bernoulli' 16 = -3617 / 510 := bernoulli'_sixteen
  have h17 : bernoulli' 17 = 0 := by
    apply bernoulli'_eq_zero_of_odd <;> decide
  rw [h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]
  have c1 : Nat.choose 18 2 = 153 := by decide
  have c2 : Nat.choose 18 4 = 3060 := by decide
  have c3 : Nat.choose 18 6 = 18564 := by decide
  have c4 : Nat.choose 18 8 = 43758 := by decide
  have c5 : Nat.choose 18 10 = 43758 := by decide
  have c6 : Nat.choose 18 12 = 18564 := by decide
  have c7 : Nat.choose 18 14 = 3060 := by decide
  have c8 : Nat.choose 18 16 = 153 := by decide
  rw [c1, c2, c3, c4, c5, c6, c7, c8]
  norm_num


lemma bernoulli'_eighteen : bernoulli' 18 = 43867 / 798 := by
  rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_eighteen

lemma a_seven : a 7 = 156 := by
  dsimp [a]
  rw [bernoulli_fourteen]
  norm_num

lemma a_nine : a 9 = 244188 := by
  dsimp [a]
  rw [bernoulli_eighteen]
  norm_num

-- lemma a_seven_decide : a 7 = 156 := by decide
-- lemma a_nine_decide : a 9 = 244188 := by decide














