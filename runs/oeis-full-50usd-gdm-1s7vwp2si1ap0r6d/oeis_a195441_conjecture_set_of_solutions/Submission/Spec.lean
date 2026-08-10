import FormalConjectures.Util.ProblemImports

open Polynomial Rat Finset Nat UniqueFactorizationMonoid

noncomputable def A195441 (n : ℕ) : ℕ := 
  let N := n + 1
  let B_num : ℚ := _root_.bernoulli N
  let P : ℚ[X] := Polynomial.bernoulli N - C B_num
  (range (N + 1)).lcm fun k => (P.coeff k).den

lemma coeff_bernoulli_sub_C_bernoulli (N : ℕ) (k : ℕ) :
    ((Polynomial.bernoulli N - C (_root_.bernoulli N)).coeff k) =
    if k = 0 then 0 else (if k ≤ N then _root_.bernoulli (N - k) * ↑(N.choose k) else 0) := by
  rw [coeff_sub]
  split_ifs with h0 hle
  · subst h0
    simp [coeff_bernoulli]
  · simp [coeff_C_ne_zero h0, coeff_bernoulli, hle]
  · simp [coeff_C_ne_zero h0, coeff_bernoulli, hle]

lemma GCDMonoid_lcm_eq_Nat_lcm (a b : ℕ) : GCDMonoid.lcm a b = Nat.lcm a b := rfl

lemma bernoulli_prime_val_6 : bernoulli' 6 = 1/42 := by
  rw [bernoulli'_def 6]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 6 2 = 15 := rfl
  have hc4 : Nat.choose 6 4 = 15 := rfl
  rw [h3, h5, bernoulli'_zero, bernoulli'_two, bernoulli'_four, hc2, hc4]
  norm_num

lemma bernoulli_prime_val_8 : bernoulli' 8 = -1/30 := by
  rw [bernoulli'_def 8]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 8 2 = 28 := rfl
  have hc4 : Nat.choose 8 4 = 70 := rfl
  have hc6 : Nat.choose 8 6 = 28 := rfl
  rw [h3, h5, h7, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, hc2, hc4, hc6]
  norm_num

lemma bernoulli_prime_val_10 : bernoulli' 10 = 5/66 := by
  rw [bernoulli'_def 10]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 10 2 = 45 := rfl
  have hc4 : Nat.choose 10 4 = 210 := rfl
  have hc6 : Nat.choose 10 6 = 210 := rfl
  have hc8 : Nat.choose 10 8 = 45 := rfl
  rw [h3, h5, h7, h9, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, hc2, hc4, hc6, hc8]
  norm_num

lemma bernoulli_prime_val_12 : bernoulli' 12 = -691/2730 := by
  rw [bernoulli'_def 12]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 12 2 = 66 := rfl
  have hc4 : Nat.choose 12 4 = 495 := rfl
  have hc6 : Nat.choose 12 6 = 924 := rfl
  have hc8 : Nat.choose 12 8 = 495 := rfl
  have hc10 : Nat.choose 12 10 = 66 := rfl
  rw [h3, h5, h7, h9, h11, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, hc2, hc4, hc6, hc8, hc10]
  norm_num

lemma bernoulli_prime_val_14 : bernoulli' 14 = 7/6 := by
  rw [bernoulli'_def 14]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 14 2 = 91 := rfl
  have hc4 : Nat.choose 14 4 = 1001 := rfl
  have hc6 : Nat.choose 14 6 = 3003 := rfl
  have hc8 : Nat.choose 14 8 = 3003 := rfl
  have hc10 : Nat.choose 14 10 = 1001 := rfl
  have hc12 : Nat.choose 14 12 = 91 := rfl
  rw [h3, h5, h7, h9, h11, h13, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, hc2, hc4, hc6, hc8, hc10, hc12]
  norm_num

lemma bernoulli_prime_val_16 : bernoulli' 16 = -3617/510 := by
  rw [bernoulli'_def 16]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 16 2 = 120 := rfl
  have hc4 : Nat.choose 16 4 = 1820 := rfl
  have hc6 : Nat.choose 16 6 = 8008 := rfl
  have hc8 : Nat.choose 16 8 = 12870 := rfl
  have hc10 : Nat.choose 16 10 = 8008 := rfl
  have hc12 : Nat.choose 16 12 = 1820 := rfl
  have hc14 : Nat.choose 16 14 = 120 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, hc2, hc4, hc6, hc8, hc10, hc12, hc14]
  norm_num

lemma bernoulli_prime_val_18 : bernoulli' 18 = 43867/798 := by
  rw [bernoulli'_def 18]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 18 2 = 153 := rfl
  have hc4 : Nat.choose 18 4 = 3060 := rfl
  have hc6 : Nat.choose 18 6 = 18564 := rfl
  have hc8 : Nat.choose 18 8 = 43758 := rfl
  have hc10 : Nat.choose 18 10 = 43758 := rfl
  have hc12 : Nat.choose 18 12 = 18564 := rfl
  have hc14 : Nat.choose 18 14 = 3060 := rfl
  have hc16 : Nat.choose 18 16 = 153 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16]
  norm_num

lemma bernoulli_prime_val_20 : bernoulli' 20 = -174611/330 := by
  rw [bernoulli'_def 20]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 20 2 = 190 := rfl
  have hc4 : Nat.choose 20 4 = 4845 := rfl
  have hc6 : Nat.choose 20 6 = 38760 := rfl
  have hc8 : Nat.choose 20 8 = 125970 := rfl
  have hc10 : Nat.choose 20 10 = 184756 := rfl
  have hc12 : Nat.choose 20 12 = 125970 := rfl
  have hc14 : Nat.choose 20 14 = 38760 := rfl
  have hc16 : Nat.choose 20 16 = 4845 := rfl
  have hc18 : Nat.choose 20 18 = 190 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18]
  norm_num

lemma bernoulli_prime_val_22 : bernoulli' 22 = 854513/138 := by
  rw [bernoulli'_def 22]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 22 2 = 231 := rfl
  have hc4 : Nat.choose 22 4 = 7315 := rfl
  have hc6 : Nat.choose 22 6 = 74613 := rfl
  have hc8 : Nat.choose 22 8 = 319770 := rfl
  have hc10 : Nat.choose 22 10 = 646646 := rfl
  have hc12 : Nat.choose 22 12 = 646646 := rfl
  have hc14 : Nat.choose 22 14 = 319770 := rfl
  have hc16 : Nat.choose 22 16 = 74613 := rfl
  have hc18 : Nat.choose 22 18 = 7315 := rfl
  have hc20 : Nat.choose 22 20 = 231 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20]
  norm_num

lemma bernoulli_prime_val_24 : bernoulli' 24 = -236364091/2730 := by
  rw [bernoulli'_def 24]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 24 2 = 276 := rfl
  have hc4 : Nat.choose 24 4 = 10626 := rfl
  have hc6 : Nat.choose 24 6 = 134596 := rfl
  have hc8 : Nat.choose 24 8 = 735471 := rfl
  have hc10 : Nat.choose 24 10 = 1961256 := rfl
  have hc12 : Nat.choose 24 12 = 2704156 := rfl
  have hc14 : Nat.choose 24 14 = 1961256 := rfl
  have hc16 : Nat.choose 24 16 = 735471 := rfl
  have hc18 : Nat.choose 24 18 = 134596 := rfl
  have hc20 : Nat.choose 24 20 = 10626 := rfl
  have hc22 : Nat.choose 24 22 = 276 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22]
  norm_num

lemma bernoulli_prime_val_26 : bernoulli' 26 = 8553103/6 := by
  rw [bernoulli'_def 26]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 26 2 = 325 := rfl
  have hc4 : Nat.choose 26 4 = 14950 := rfl
  have hc6 : Nat.choose 26 6 = 230230 := rfl
  have hc8 : Nat.choose 26 8 = 1562275 := rfl
  have hc10 : Nat.choose 26 10 = 5311735 := rfl
  have hc12 : Nat.choose 26 12 = 9657700 := rfl
  have hc14 : Nat.choose 26 14 = 9657700 := rfl
  have hc16 : Nat.choose 26 16 = 5311735 := rfl
  have hc18 : Nat.choose 26 18 = 1562275 := rfl
  have hc20 : Nat.choose 26 20 = 230230 := rfl
  have hc22 : Nat.choose 26 22 = 14950 := rfl
  have hc24 : Nat.choose 26 24 = 325 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24]
  norm_num

lemma bernoulli_prime_val_28 : bernoulli' 28 = -23749461029/870 := by
  rw [bernoulli'_def 28]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 28 2 = 378 := rfl
  have hc4 : Nat.choose 28 4 = 20475 := rfl
  have hc6 : Nat.choose 28 6 = 376740 := rfl
  have hc8 : Nat.choose 28 8 = 3108105 := rfl
  have hc10 : Nat.choose 28 10 = 13123110 := rfl
  have hc12 : Nat.choose 28 12 = 30421755 := rfl
  have hc14 : Nat.choose 28 14 = 40116600 := rfl
  have hc16 : Nat.choose 28 16 = 30421755 := rfl
  have hc18 : Nat.choose 28 18 = 13123110 := rfl
  have hc20 : Nat.choose 28 20 = 3108105 := rfl
  have hc22 : Nat.choose 28 22 = 376740 := rfl
  have hc24 : Nat.choose 28 24 = 20475 := rfl
  have hc26 : Nat.choose 28 26 = 378 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26]
  norm_num

lemma bernoulli_prime_val_30 : bernoulli' 30 = 8615841276005/14322 := by
  rw [bernoulli'_def 30]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 30 2 = 435 := rfl
  have hc4 : Nat.choose 30 4 = 27405 := rfl
  have hc6 : Nat.choose 30 6 = 593775 := rfl
  have hc8 : Nat.choose 30 8 = 5852925 := rfl
  have hc10 : Nat.choose 30 10 = 30045015 := rfl
  have hc12 : Nat.choose 30 12 = 86493225 := rfl
  have hc14 : Nat.choose 30 14 = 145422675 := rfl
  have hc16 : Nat.choose 30 16 = 145422675 := rfl
  have hc18 : Nat.choose 30 18 = 86493225 := rfl
  have hc20 : Nat.choose 30 20 = 30045015 := rfl
  have hc22 : Nat.choose 30 22 = 5852925 := rfl
  have hc24 : Nat.choose 30 24 = 593775 := rfl
  have hc26 : Nat.choose 30 26 = 27405 := rfl
  have hc28 : Nat.choose 30 28 = 435 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28]
  norm_num

lemma bernoulli_prime_val_32 : bernoulli' 32 = -7709321041217/510 := by
  rw [bernoulli'_def 32]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 32 2 = 496 := rfl
  have hc4 : Nat.choose 32 4 = 35960 := rfl
  have hc6 : Nat.choose 32 6 = 906192 := rfl
  have hc8 : Nat.choose 32 8 = 10518300 := rfl
  have hc10 : Nat.choose 32 10 = 64512240 := rfl
  have hc12 : Nat.choose 32 12 = 225792840 := rfl
  have hc14 : Nat.choose 32 14 = 471435600 := rfl
  have hc16 : Nat.choose 32 16 = 601080390 := rfl
  have hc18 : Nat.choose 32 18 = 471435600 := rfl
  have hc20 : Nat.choose 32 20 = 225792840 := rfl
  have hc22 : Nat.choose 32 22 = 64512240 := rfl
  have hc24 : Nat.choose 32 24 = 10518300 := rfl
  have hc26 : Nat.choose 32 26 = 906192 := rfl
  have hc28 : Nat.choose 32 28 = 35960 := rfl
  have hc30 : Nat.choose 32 30 = 496 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30]
  norm_num

lemma bernoulli_prime_val_34 : bernoulli' 34 = 2577687858367/6 := by
  rw [bernoulli'_def 34]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 34 2 = 561 := rfl
  have hc4 : Nat.choose 34 4 = 46376 := rfl
  have hc6 : Nat.choose 34 6 = 1344904 := rfl
  have hc8 : Nat.choose 34 8 = 18156204 := rfl
  have hc10 : Nat.choose 34 10 = 131128140 := rfl
  have hc12 : Nat.choose 34 12 = 548354040 := rfl
  have hc14 : Nat.choose 34 14 = 1391975640 := rfl
  have hc16 : Nat.choose 34 16 = 2203961430 := rfl
  have hc18 : Nat.choose 34 18 = 2203961430 := rfl
  have hc20 : Nat.choose 34 20 = 1391975640 := rfl
  have hc22 : Nat.choose 34 22 = 548354040 := rfl
  have hc24 : Nat.choose 34 24 = 131128140 := rfl
  have hc26 : Nat.choose 34 26 = 18156204 := rfl
  have hc28 : Nat.choose 34 28 = 1344904 := rfl
  have hc30 : Nat.choose 34 30 = 46376 := rfl
  have hc32 : Nat.choose 34 32 = 561 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32]
  norm_num

lemma bernoulli_prime_val_36 : bernoulli' 36 = -26315271553053477373/1919190 := by
  rw [bernoulli'_def 36]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 36 2 = 630 := rfl
  have hc4 : Nat.choose 36 4 = 58905 := rfl
  have hc6 : Nat.choose 36 6 = 1947792 := rfl
  have hc8 : Nat.choose 36 8 = 30260340 := rfl
  have hc10 : Nat.choose 36 10 = 254186856 := rfl
  have hc12 : Nat.choose 36 12 = 1251677700 := rfl
  have hc14 : Nat.choose 36 14 = 3796297200 := rfl
  have hc16 : Nat.choose 36 16 = 7307872110 := rfl
  have hc18 : Nat.choose 36 18 = 9075135300 := rfl
  have hc20 : Nat.choose 36 20 = 7307872110 := rfl
  have hc22 : Nat.choose 36 22 = 3796297200 := rfl
  have hc24 : Nat.choose 36 24 = 1251677700 := rfl
  have hc26 : Nat.choose 36 26 = 254186856 := rfl
  have hc28 : Nat.choose 36 28 = 30260340 := rfl
  have hc30 : Nat.choose 36 30 = 1947792 := rfl
  have hc32 : Nat.choose 36 32 = 58905 := rfl
  have hc34 : Nat.choose 36 34 = 630 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34]
  norm_num

lemma bernoulli_prime_val_38 : bernoulli' 38 = 2929993913841559/6 := by
  rw [bernoulli'_def 38]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 38 2 = 703 := rfl
  have hc4 : Nat.choose 38 4 = 73815 := rfl
  have hc6 : Nat.choose 38 6 = 2760681 := rfl
  have hc8 : Nat.choose 38 8 = 48903492 := rfl
  have hc10 : Nat.choose 38 10 = 472733756 := rfl
  have hc12 : Nat.choose 38 12 = 2707475148 := rfl
  have hc14 : Nat.choose 38 14 = 9669554100 := rfl
  have hc16 : Nat.choose 38 16 = 22239974430 := rfl
  have hc18 : Nat.choose 38 18 = 33578000610 := rfl
  have hc20 : Nat.choose 38 20 = 33578000610 := rfl
  have hc22 : Nat.choose 38 22 = 22239974430 := rfl
  have hc24 : Nat.choose 38 24 = 9669554100 := rfl
  have hc26 : Nat.choose 38 26 = 2707475148 := rfl
  have hc28 : Nat.choose 38 28 = 472733756 := rfl
  have hc30 : Nat.choose 38 30 = 48903492 := rfl
  have hc32 : Nat.choose 38 32 = 2760681 := rfl
  have hc34 : Nat.choose 38 34 = 73815 := rfl
  have hc36 : Nat.choose 38 36 = 703 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36]
  norm_num

lemma bernoulli_prime_val_40 : bernoulli' 40 = -261082718496449122051/13530 := by
  rw [bernoulli'_def 40]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 40 2 = 780 := rfl
  have hc4 : Nat.choose 40 4 = 91390 := rfl
  have hc6 : Nat.choose 40 6 = 3838380 := rfl
  have hc8 : Nat.choose 40 8 = 76904685 := rfl
  have hc10 : Nat.choose 40 10 = 847660528 := rfl
  have hc12 : Nat.choose 40 12 = 5586853480 := rfl
  have hc14 : Nat.choose 40 14 = 23206929840 := rfl
  have hc16 : Nat.choose 40 16 = 62852101650 := rfl
  have hc18 : Nat.choose 40 18 = 113380261800 := rfl
  have hc20 : Nat.choose 40 20 = 137846528820 := rfl
  have hc22 : Nat.choose 40 22 = 113380261800 := rfl
  have hc24 : Nat.choose 40 24 = 62852101650 := rfl
  have hc26 : Nat.choose 40 26 = 23206929840 := rfl
  have hc28 : Nat.choose 40 28 = 5586853480 := rfl
  have hc30 : Nat.choose 40 30 = 847660528 := rfl
  have hc32 : Nat.choose 40 32 = 76904685 := rfl
  have hc34 : Nat.choose 40 34 = 3838380 := rfl
  have hc36 : Nat.choose 40 36 = 91390 := rfl
  have hc38 : Nat.choose 40 38 = 780 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38]
  norm_num

lemma bernoulli_prime_val_42 : bernoulli' 42 = 1520097643918070802691/1806 := by
  rw [bernoulli'_def 42]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 42 2 = 861 := rfl
  have hc4 : Nat.choose 42 4 = 111930 := rfl
  have hc6 : Nat.choose 42 6 = 5245786 := rfl
  have hc8 : Nat.choose 42 8 = 118030185 := rfl
  have hc10 : Nat.choose 42 10 = 1471442973 := rfl
  have hc12 : Nat.choose 42 12 = 11058116888 := rfl
  have hc14 : Nat.choose 42 14 = 52860229080 := rfl
  have hc16 : Nat.choose 42 16 = 166509721602 := rfl
  have hc18 : Nat.choose 42 18 = 353697121050 := rfl
  have hc20 : Nat.choose 42 20 = 513791607420 := rfl
  have hc22 : Nat.choose 42 22 = 513791607420 := rfl
  have hc24 : Nat.choose 42 24 = 353697121050 := rfl
  have hc26 : Nat.choose 42 26 = 166509721602 := rfl
  have hc28 : Nat.choose 42 28 = 52860229080 := rfl
  have hc30 : Nat.choose 42 30 = 11058116888 := rfl
  have hc32 : Nat.choose 42 32 = 1471442973 := rfl
  have hc34 : Nat.choose 42 34 = 118030185 := rfl
  have hc36 : Nat.choose 42 36 = 5245786 := rfl
  have hc38 : Nat.choose 42 38 = 111930 := rfl
  have hc40 : Nat.choose 42 40 = 861 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40]
  norm_num

lemma bernoulli_prime_val_44 : bernoulli' 44 = -27833269579301024235023/690 := by
  rw [bernoulli'_def 44]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 44 2 = 946 := rfl
  have hc4 : Nat.choose 44 4 = 135751 := rfl
  have hc6 : Nat.choose 44 6 = 7059052 := rfl
  have hc8 : Nat.choose 44 8 = 177232627 := rfl
  have hc10 : Nat.choose 44 10 = 2481256778 := rfl
  have hc12 : Nat.choose 44 12 = 21090682613 := rfl
  have hc14 : Nat.choose 44 14 = 114955808528 := rfl
  have hc16 : Nat.choose 44 16 = 416714805914 := rfl
  have hc18 : Nat.choose 44 18 = 1029530696964 := rfl
  have hc20 : Nat.choose 44 20 = 1761039350070 := rfl
  have hc22 : Nat.choose 44 22 = 2104098963720 := rfl
  have hc24 : Nat.choose 44 24 = 1761039350070 := rfl
  have hc26 : Nat.choose 44 26 = 1029530696964 := rfl
  have hc28 : Nat.choose 44 28 = 416714805914 := rfl
  have hc30 : Nat.choose 44 30 = 114955808528 := rfl
  have hc32 : Nat.choose 44 32 = 21090682613 := rfl
  have hc34 : Nat.choose 44 34 = 2481256778 := rfl
  have hc36 : Nat.choose 44 36 = 177232627 := rfl
  have hc38 : Nat.choose 44 38 = 7059052 := rfl
  have hc40 : Nat.choose 44 40 = 135751 := rfl
  have hc42 : Nat.choose 44 42 = 946 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42]
  norm_num

lemma bernoulli_prime_val_46 : bernoulli' 46 = 596451111593912163277961/282 := by
  rw [bernoulli'_def 46]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 46 2 = 1035 := rfl
  have hc4 : Nat.choose 46 4 = 163185 := rfl
  have hc6 : Nat.choose 46 6 = 9366819 := rfl
  have hc8 : Nat.choose 46 8 = 260932815 := rfl
  have hc10 : Nat.choose 46 10 = 4076350421 := rfl
  have hc12 : Nat.choose 46 12 = 38910617655 := rfl
  have hc14 : Nat.choose 46 14 = 239877544005 := rfl
  have hc16 : Nat.choose 46 16 = 991493848554 := rfl
  have hc18 : Nat.choose 46 18 = 2818953098830 := rfl
  have hc20 : Nat.choose 46 20 = 5608233007146 := rfl
  have hc22 : Nat.choose 46 22 = 7890371113950 := rfl
  have hc24 : Nat.choose 46 24 = 7890371113950 := rfl
  have hc26 : Nat.choose 46 26 = 5608233007146 := rfl
  have hc28 : Nat.choose 46 28 = 2818953098830 := rfl
  have hc30 : Nat.choose 46 30 = 991493848554 := rfl
  have hc32 : Nat.choose 46 32 = 239877544005 := rfl
  have hc34 : Nat.choose 46 34 = 38910617655 := rfl
  have hc36 : Nat.choose 46 36 = 4076350421 := rfl
  have hc38 : Nat.choose 46 38 = 260932815 := rfl
  have hc40 : Nat.choose 46 40 = 9366819 := rfl
  have hc42 : Nat.choose 46 42 = 163185 := rfl
  have hc44 : Nat.choose 46 44 = 1035 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44]
  norm_num

lemma bernoulli_prime_val_48 : bernoulli' 48 = -5609403368997817686249127547/46410 := by
  rw [bernoulli'_def 48]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 48 2 = 1128 := rfl
  have hc4 : Nat.choose 48 4 = 194580 := rfl
  have hc6 : Nat.choose 48 6 = 12271512 := rfl
  have hc8 : Nat.choose 48 8 = 377348994 := rfl
  have hc10 : Nat.choose 48 10 = 6540715896 := rfl
  have hc12 : Nat.choose 48 12 = 69668534468 := rfl
  have hc14 : Nat.choose 48 14 = 482320623240 := rfl
  have hc16 : Nat.choose 48 16 = 2254848913647 := rfl
  have hc18 : Nat.choose 48 18 = 7309837001104 := rfl
  have hc20 : Nat.choose 48 20 = 16735679449896 := rfl
  have hc22 : Nat.choose 48 22 = 27385657281648 := rfl
  have hc24 : Nat.choose 48 24 = 32247603683100 := rfl
  have hc26 : Nat.choose 48 26 = 27385657281648 := rfl
  have hc28 : Nat.choose 48 28 = 16735679449896 := rfl
  have hc30 : Nat.choose 48 30 = 7309837001104 := rfl
  have hc32 : Nat.choose 48 32 = 2254848913647 := rfl
  have hc34 : Nat.choose 48 34 = 482320623240 := rfl
  have hc36 : Nat.choose 48 36 = 69668534468 := rfl
  have hc38 : Nat.choose 48 38 = 6540715896 := rfl
  have hc40 : Nat.choose 48 40 = 377348994 := rfl
  have hc42 : Nat.choose 48 42 = 12271512 := rfl
  have hc44 : Nat.choose 48 44 = 194580 := rfl
  have hc46 : Nat.choose 48 46 = 1128 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46]
  norm_num

lemma bernoulli_prime_val_50 : bernoulli' 50 = 495057205241079648212477525/66 := by
  rw [bernoulli'_def 50]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 50 2 = 1225 := rfl
  have hc4 : Nat.choose 50 4 = 230300 := rfl
  have hc6 : Nat.choose 50 6 = 15890700 := rfl
  have hc8 : Nat.choose 50 8 = 536878650 := rfl
  have hc10 : Nat.choose 50 10 = 10272278170 := rfl
  have hc12 : Nat.choose 50 12 = 121399651100 := rfl
  have hc14 : Nat.choose 50 14 = 937845656300 := rfl
  have hc16 : Nat.choose 50 16 = 4923689695575 := rfl
  have hc18 : Nat.choose 50 18 = 18053528883775 := rfl
  have hc20 : Nat.choose 50 20 = 47129212243960 := rfl
  have hc22 : Nat.choose 50 22 = 88749815264600 := rfl
  have hc24 : Nat.choose 50 24 = 121548660036300 := rfl
  have hc26 : Nat.choose 50 26 = 121548660036300 := rfl
  have hc28 : Nat.choose 50 28 = 88749815264600 := rfl
  have hc30 : Nat.choose 50 30 = 47129212243960 := rfl
  have hc32 : Nat.choose 50 32 = 18053528883775 := rfl
  have hc34 : Nat.choose 50 34 = 4923689695575 := rfl
  have hc36 : Nat.choose 50 36 = 937845656300 := rfl
  have hc38 : Nat.choose 50 38 = 121399651100 := rfl
  have hc40 : Nat.choose 50 40 = 10272278170 := rfl
  have hc42 : Nat.choose 50 42 = 536878650 := rfl
  have hc44 : Nat.choose 50 44 = 15890700 := rfl
  have hc46 : Nat.choose 50 46 = 230300 := rfl
  have hc48 : Nat.choose 50 48 = 1225 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48]
  norm_num

lemma bernoulli_prime_val_52 : bernoulli' 52 = -801165718135489957347924991853/1590 := by
  rw [bernoulli'_def 52]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h51 : bernoulli' 51 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 52 2 = 1326 := rfl
  have hc4 : Nat.choose 52 4 = 270725 := rfl
  have hc6 : Nat.choose 52 6 = 20358520 := rfl
  have hc8 : Nat.choose 52 8 = 752538150 := rfl
  have hc10 : Nat.choose 52 10 = 15820024220 := rfl
  have hc12 : Nat.choose 52 12 = 206379406870 := rfl
  have hc14 : Nat.choose 52 14 = 1768966344600 := rfl
  have hc16 : Nat.choose 52 16 = 10363194502115 := rfl
  have hc18 : Nat.choose 52 18 = 42671977361650 := rfl
  have hc20 : Nat.choose 52 20 = 125994627894135 := rfl
  have hc22 : Nat.choose 52 22 = 270533919634160 := rfl
  have hc24 : Nat.choose 52 24 = 426384982032100 := rfl
  have hc26 : Nat.choose 52 26 = 495918532948104 := rfl
  have hc28 : Nat.choose 52 28 = 426384982032100 := rfl
  have hc30 : Nat.choose 52 30 = 270533919634160 := rfl
  have hc32 : Nat.choose 52 32 = 125994627894135 := rfl
  have hc34 : Nat.choose 52 34 = 42671977361650 := rfl
  have hc36 : Nat.choose 52 36 = 10363194502115 := rfl
  have hc38 : Nat.choose 52 38 = 1768966344600 := rfl
  have hc40 : Nat.choose 52 40 = 206379406870 := rfl
  have hc42 : Nat.choose 52 42 = 15820024220 := rfl
  have hc44 : Nat.choose 52 44 = 752538150 := rfl
  have hc46 : Nat.choose 52 46 = 20358520 := rfl
  have hc48 : Nat.choose 52 48 = 270725 := rfl
  have hc50 : Nat.choose 52 50 = 1326 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, bernoulli_prime_val_50, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48, hc50]
  norm_num

lemma bernoulli_prime_val_54 : bernoulli' 54 = 29149963634884862421418123812691/798 := by
  rw [bernoulli'_def 54]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h51 : bernoulli' 51 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h53 : bernoulli' 53 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 54 2 = 1431 := rfl
  have hc4 : Nat.choose 54 4 = 316251 := rfl
  have hc6 : Nat.choose 54 6 = 25827165 := rfl
  have hc8 : Nat.choose 54 8 = 1040465790 := rfl
  have hc10 : Nat.choose 54 10 = 23930713170 := rfl
  have hc12 : Nat.choose 54 12 = 343006888770 := rfl
  have hc14 : Nat.choose 54 14 = 3245372870670 := rfl
  have hc16 : Nat.choose 54 16 = 21094923659355 := rfl
  have hc18 : Nat.choose 54 18 = 96926348578605 := rfl
  have hc20 : Nat.choose 54 20 = 321387366339585 := rfl
  have hc22 : Nat.choose 54 22 = 780512175396135 := rfl
  have hc24 : Nat.choose 54 24 = 1402659561581460 := rfl
  have hc26 : Nat.choose 54 26 = 1877405874732108 := rfl
  have hc28 : Nat.choose 54 28 = 1877405874732108 := rfl
  have hc30 : Nat.choose 54 30 = 1402659561581460 := rfl
  have hc32 : Nat.choose 54 32 = 780512175396135 := rfl
  have hc34 : Nat.choose 54 34 = 321387366339585 := rfl
  have hc36 : Nat.choose 54 36 = 96926348578605 := rfl
  have hc38 : Nat.choose 54 38 = 21094923659355 := rfl
  have hc40 : Nat.choose 54 40 = 3245372870670 := rfl
  have hc42 : Nat.choose 54 42 = 343006888770 := rfl
  have hc44 : Nat.choose 54 44 = 23930713170 := rfl
  have hc46 : Nat.choose 54 46 = 1040465790 := rfl
  have hc48 : Nat.choose 54 48 = 25827165 := rfl
  have hc50 : Nat.choose 54 50 = 316251 := rfl
  have hc52 : Nat.choose 54 52 = 1431 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, bernoulli_prime_val_50, bernoulli_prime_val_52, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48, hc50, hc52]
  norm_num

lemma bernoulli_prime_val_56 : bernoulli' 56 = -2479392929313226753685415739663229/870 := by
  rw [bernoulli'_def 56]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h51 : bernoulli' 51 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h53 : bernoulli' 53 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h55 : bernoulli' 55 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 56 2 = 1540 := rfl
  have hc4 : Nat.choose 56 4 = 367290 := rfl
  have hc6 : Nat.choose 56 6 = 32468436 := rfl
  have hc8 : Nat.choose 56 8 = 1420494075 := rfl
  have hc10 : Nat.choose 56 10 = 35607051480 := rfl
  have hc12 : Nat.choose 56 12 = 558383307300 := rfl
  have hc14 : Nat.choose 56 14 = 5804731963800 := rfl
  have hc16 : Nat.choose 56 16 = 41648951840265 := rfl
  have hc18 : Nat.choose 56 18 = 212327989773900 := rfl
  have hc20 : Nat.choose 56 20 = 785613562163430 := rfl
  have hc22 : Nat.choose 56 22 = 2142582442263900 := rfl
  have hc24 : Nat.choose 56 24 = 4355031703297275 := rfl
  have hc26 : Nat.choose 56 26 = 6646448384109072 := rfl
  have hc28 : Nat.choose 56 28 = 7648690600760440 := rfl
  have hc30 : Nat.choose 56 30 = 6646448384109072 := rfl
  have hc32 : Nat.choose 56 32 = 4355031703297275 := rfl
  have hc34 : Nat.choose 56 34 = 2142582442263900 := rfl
  have hc36 : Nat.choose 56 36 = 785613562163430 := rfl
  have hc38 : Nat.choose 56 38 = 212327989773900 := rfl
  have hc40 : Nat.choose 56 40 = 41648951840265 := rfl
  have hc42 : Nat.choose 56 42 = 5804731963800 := rfl
  have hc44 : Nat.choose 56 44 = 558383307300 := rfl
  have hc46 : Nat.choose 56 46 = 35607051480 := rfl
  have hc48 : Nat.choose 56 48 = 1420494075 := rfl
  have hc50 : Nat.choose 56 50 = 32468436 := rfl
  have hc52 : Nat.choose 56 52 = 367290 := rfl
  have hc54 : Nat.choose 56 54 = 1540 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, h55, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, bernoulli_prime_val_50, bernoulli_prime_val_52, bernoulli_prime_val_54, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48, hc50, hc52, hc54]
  norm_num

lemma bernoulli_prime_val_58 : bernoulli' 58 = 84483613348880041862046775994036021/354 := by
  rw [bernoulli'_def 58]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h51 : bernoulli' 51 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h53 : bernoulli' 53 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h55 : bernoulli' 55 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h57 : bernoulli' 57 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 58 2 = 1653 := rfl
  have hc4 : Nat.choose 58 4 = 424270 := rfl
  have hc6 : Nat.choose 58 6 = 40475358 := rfl
  have hc8 : Nat.choose 58 8 = 1916797311 := rfl
  have hc10 : Nat.choose 58 10 = 52179482355 := rfl
  have hc12 : Nat.choose 58 12 = 891794789340 := rfl
  have hc14 : Nat.choose 58 14 = 10142940735900 := rfl
  have hc16 : Nat.choose 58 16 = 79960182801345 := rfl
  have hc18 : Nat.choose 58 18 = 449972009097765 := rfl
  have hc20 : Nat.choose 58 20 = 1847253511032930 := rfl
  have hc22 : Nat.choose 58 22 = 5621728217559090 := rfl
  have hc24 : Nat.choose 58 24 = 12832205713993575 := rfl
  have hc26 : Nat.choose 58 26 = 22150361247847371 := rfl
  have hc28 : Nat.choose 58 28 = 29065024282889672 := rfl
  have hc30 : Nat.choose 58 30 = 29065024282889672 := rfl
  have hc32 : Nat.choose 58 32 = 22150361247847371 := rfl
  have hc34 : Nat.choose 58 34 = 12832205713993575 := rfl
  have hc36 : Nat.choose 58 36 = 5621728217559090 := rfl
  have hc38 : Nat.choose 58 38 = 1847253511032930 := rfl
  have hc40 : Nat.choose 58 40 = 449972009097765 := rfl
  have hc42 : Nat.choose 58 42 = 79960182801345 := rfl
  have hc44 : Nat.choose 58 44 = 10142940735900 := rfl
  have hc46 : Nat.choose 58 46 = 891794789340 := rfl
  have hc48 : Nat.choose 58 48 = 52179482355 := rfl
  have hc50 : Nat.choose 58 50 = 1916797311 := rfl
  have hc52 : Nat.choose 58 52 = 40475358 := rfl
  have hc54 : Nat.choose 58 54 = 424270 := rfl
  have hc56 : Nat.choose 58 56 = 1653 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, h55, h57, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, bernoulli_prime_val_50, bernoulli_prime_val_52, bernoulli_prime_val_54, bernoulli_prime_val_56, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48, hc50, hc52, hc54, hc56]
  norm_num

lemma bernoulli_prime_val_60 : bernoulli' 60 = -1215233140483755572040304994079820246041491/56786730 := by
  rw [bernoulli'_def 60]
  simp only [sum_range_succ, sum_range_zero]
  have h3 : bernoulli' 3 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h5 : bernoulli' 5 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h7 : bernoulli' 7 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h9 : bernoulli' 9 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h11 : bernoulli' 11 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h13 : bernoulli' 13 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h15 : bernoulli' 15 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h17 : bernoulli' 17 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h19 : bernoulli' 19 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h21 : bernoulli' 21 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h23 : bernoulli' 23 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h25 : bernoulli' 25 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h27 : bernoulli' 27 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h29 : bernoulli' 29 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h31 : bernoulli' 31 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h33 : bernoulli' 33 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h35 : bernoulli' 35 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h37 : bernoulli' 37 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h39 : bernoulli' 39 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h41 : bernoulli' 41 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h43 : bernoulli' 43 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h45 : bernoulli' 45 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h47 : bernoulli' 47 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h49 : bernoulli' 49 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h51 : bernoulli' 51 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h53 : bernoulli' 53 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h55 : bernoulli' 55 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h57 : bernoulli' 57 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have h59 : bernoulli' 59 = 0 := by apply bernoulli'_eq_zero_of_odd <;> decide
  have hc2 : Nat.choose 60 2 = 1770 := rfl
  have hc4 : Nat.choose 60 4 = 487635 := rfl
  have hc6 : Nat.choose 60 6 = 50063860 := rfl
  have hc8 : Nat.choose 60 8 = 2558620845 := rfl
  have hc10 : Nat.choose 60 10 = 75394027566 := rfl
  have hc12 : Nat.choose 60 12 = 1399358844975 := rfl
  have hc14 : Nat.choose 60 14 = 17345898649800 := rfl
  have hc16 : Nat.choose 60 16 = 149608375854525 := rfl
  have hc18 : Nat.choose 60 18 = 925029565741050 := rfl
  have hc20 : Nat.choose 60 20 = 4191844505805495 := rfl
  have hc22 : Nat.choose 60 22 = 14154280149473100 := rfl
  have hc24 : Nat.choose 60 24 = 36052387482172425 := rfl
  have hc26 : Nat.choose 60 26 = 69886166503903470 := rfl
  have hc28 : Nat.choose 60 28 = 103719945525634515 := rfl
  have hc30 : Nat.choose 60 30 = 118264581564861424 := rfl
  have hc32 : Nat.choose 60 32 = 103719945525634515 := rfl
  have hc34 : Nat.choose 60 34 = 69886166503903470 := rfl
  have hc36 : Nat.choose 60 36 = 36052387482172425 := rfl
  have hc38 : Nat.choose 60 38 = 14154280149473100 := rfl
  have hc40 : Nat.choose 60 40 = 4191844505805495 := rfl
  have hc42 : Nat.choose 60 42 = 925029565741050 := rfl
  have hc44 : Nat.choose 60 44 = 149608375854525 := rfl
  have hc46 : Nat.choose 60 46 = 17345898649800 := rfl
  have hc48 : Nat.choose 60 48 = 1399358844975 := rfl
  have hc50 : Nat.choose 60 50 = 75394027566 := rfl
  have hc52 : Nat.choose 60 52 = 2558620845 := rfl
  have hc54 : Nat.choose 60 54 = 50063860 := rfl
  have hc56 : Nat.choose 60 56 = 487635 := rfl
  have hc58 : Nat.choose 60 58 = 1770 := rfl
  rw [h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, h55, h57, h59, bernoulli'_zero, bernoulli'_two, bernoulli'_four, bernoulli_prime_val_6, bernoulli_prime_val_8, bernoulli_prime_val_10, bernoulli_prime_val_12, bernoulli_prime_val_14, bernoulli_prime_val_16, bernoulli_prime_val_18, bernoulli_prime_val_20, bernoulli_prime_val_22, bernoulli_prime_val_24, bernoulli_prime_val_26, bernoulli_prime_val_28, bernoulli_prime_val_30, bernoulli_prime_val_32, bernoulli_prime_val_34, bernoulli_prime_val_36, bernoulli_prime_val_38, bernoulli_prime_val_40, bernoulli_prime_val_42, bernoulli_prime_val_44, bernoulli_prime_val_46, bernoulli_prime_val_48, bernoulli_prime_val_50, bernoulli_prime_val_52, bernoulli_prime_val_54, bernoulli_prime_val_56, bernoulli_prime_val_58, hc2, hc4, hc6, hc8, hc10, hc12, hc14, hc16, hc18, hc20, hc22, hc24, hc26, hc28, hc30, hc32, hc34, hc36, hc38, hc40, hc42, hc44, hc46, hc48, hc50, hc52, hc54, hc56, hc58]
  norm_num

lemma bernoulli_val_0 : _root_.bernoulli 0 = 1 := bernoulli_zero
lemma bernoulli_val_2 : _root_.bernoulli 2 = 1/6 := by
  rw [bernoulli_two]
  norm_num

lemma bernoulli_val_4 : _root_.bernoulli 4 = -1/30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli'_four

lemma bernoulli_val_6 : _root_.bernoulli 6 = 1/42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_6

lemma bernoulli_val_8 : _root_.bernoulli 8 = -1/30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_8

lemma bernoulli_val_10 : _root_.bernoulli 10 = 5/66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_10

lemma bernoulli_val_12 : _root_.bernoulli 12 = -691/2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_12

lemma bernoulli_val_14 : _root_.bernoulli 14 = 7/6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_14

lemma bernoulli_val_16 : _root_.bernoulli 16 = -3617/510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_16

lemma bernoulli_val_18 : _root_.bernoulli 18 = 43867/798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_18

lemma bernoulli_val_20 : _root_.bernoulli 20 = -174611/330 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_20

lemma bernoulli_val_22 : _root_.bernoulli 22 = 854513/138 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_22

lemma bernoulli_val_24 : _root_.bernoulli 24 = -236364091/2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_24

lemma bernoulli_val_26 : _root_.bernoulli 26 = 8553103/6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_26

lemma bernoulli_val_28 : _root_.bernoulli 28 = -23749461029/870 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_28

lemma bernoulli_val_30 : _root_.bernoulli 30 = 8615841276005/14322 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_30

lemma bernoulli_val_32 : _root_.bernoulli 32 = -7709321041217/510 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_32

lemma bernoulli_val_34 : _root_.bernoulli 34 = 2577687858367/6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_34

lemma bernoulli_val_36 : _root_.bernoulli 36 = -26315271553053477373/1919190 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_36

lemma bernoulli_val_38 : _root_.bernoulli 38 = 2929993913841559/6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_38

lemma bernoulli_val_40 : _root_.bernoulli 40 = -261082718496449122051/13530 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_40

lemma bernoulli_val_42 : _root_.bernoulli 42 = 1520097643918070802691/1806 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_42

lemma bernoulli_val_44 : _root_.bernoulli 44 = -27833269579301024235023/690 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_44

lemma bernoulli_val_46 : _root_.bernoulli 46 = 596451111593912163277961/282 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_46

lemma bernoulli_val_48 : _root_.bernoulli 48 = -5609403368997817686249127547/46410 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_48

lemma bernoulli_val_50 : _root_.bernoulli 50 = 495057205241079648212477525/66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_50

lemma bernoulli_val_52 : _root_.bernoulli 52 = -801165718135489957347924991853/1590 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_52

lemma bernoulli_val_54 : _root_.bernoulli 54 = 29149963634884862421418123812691/798 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_54

lemma bernoulli_val_56 : _root_.bernoulli 56 = -2479392929313226753685415739663229/870 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_56

lemma bernoulli_val_58 : _root_.bernoulli 58 = 84483613348880041862046775994036021/354 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_58

lemma bernoulli_val_60 : _root_.bernoulli 60 = -1215233140483755572040304994079820246041491/56786730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide)]
  exact bernoulli_prime_val_60



theorem radical_0 : radical 0 = 1 := radical_zero
theorem radical_1 : radical 1 = 1 := radical_one
theorem radical_2 : radical 2 = 2 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_3 : radical 3 = 3 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_4 : radical 4 = 2 := by
  have h1 : 4 = 2 ^ 2 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_2]
  · decide
theorem radical_5 : radical 5 = 5 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_6 : radical 6 = 6 := by
  have h1 : 6 = 2 * 3 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_3]
  try rfl
theorem radical_7 : radical 7 = 7 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_8 : radical 8 = 2 := by
  have h1 : 8 = 2 ^ 3 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_2]
  · decide
theorem radical_9 : radical 9 = 3 := by
  have h1 : 9 = 3 ^ 2 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_3]
  · decide
theorem radical_10 : radical 10 = 10 := by
  have h1 : 10 = 2 * 5 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_5]
  try rfl
theorem radical_11 : radical 11 = 11 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_12 : radical 12 = 6 := by
  have h1 : 12 = 4 * 3 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_3]
  try rfl
theorem radical_13 : radical 13 = 13 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_14 : radical 14 = 14 := by
  have h1 : 14 = 2 * 7 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_7]
  try rfl
theorem radical_15 : radical 15 = 15 := by
  have h1 : 15 = 3 * 5 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_5]
  try rfl
theorem radical_16 : radical 16 = 2 := by
  have h1 : 16 = 2 ^ 4 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_2]
  · decide
theorem radical_17 : radical 17 = 17 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_18 : radical 18 = 6 := by
  have h1 : 18 = 2 * 9 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_9]
  try rfl
theorem radical_19 : radical 19 = 19 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_20 : radical 20 = 10 := by
  have h1 : 20 = 4 * 5 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_5]
  try rfl
theorem radical_21 : radical 21 = 21 := by
  have h1 : 21 = 3 * 7 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_7]
  try rfl
theorem radical_22 : radical 22 = 22 := by
  have h1 : 22 = 2 * 11 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_11]
  try rfl
theorem radical_23 : radical 23 = 23 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_24 : radical 24 = 6 := by
  have h1 : 24 = 8 * 3 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_8, radical_3]
  try rfl
theorem radical_25 : radical 25 = 5 := by
  have h1 : 25 = 5 ^ 2 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_5]
  · decide
theorem radical_26 : radical 26 = 26 := by
  have h1 : 26 = 2 * 13 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_13]
  try rfl
theorem radical_27 : radical 27 = 3 := by
  have h1 : 27 = 3 ^ 3 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_3]
  · decide
theorem radical_28 : radical 28 = 14 := by
  have h1 : 28 = 4 * 7 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_7]
  try rfl
theorem radical_29 : radical 29 = 29 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_30 : radical 30 = 30 := by
  have h1 : 30 = 2 * 15 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_15]
  try rfl
theorem radical_31 : radical 31 = 31 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_32 : radical 32 = 2 := by
  have h1 : 32 = 2 ^ 5 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_2]
  · decide
theorem radical_33 : radical 33 = 33 := by
  have h1 : 33 = 3 * 11 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_11]
  try rfl
theorem radical_34 : radical 34 = 34 := by
  have h1 : 34 = 2 * 17 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_17]
  try rfl
theorem radical_35 : radical 35 = 35 := by
  have h1 : 35 = 5 * 7 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_5, radical_7]
  try rfl
theorem radical_36 : radical 36 = 6 := by
  have h1 : 36 = 4 * 9 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_9]
  try rfl
theorem radical_37 : radical 37 = 37 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_38 : radical 38 = 38 := by
  have h1 : 38 = 2 * 19 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_19]
  try rfl
theorem radical_39 : radical 39 = 39 := by
  have h1 : 39 = 3 * 13 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_13]
  try rfl
theorem radical_40 : radical 40 = 10 := by
  have h1 : 40 = 8 * 5 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_8, radical_5]
  try rfl
theorem radical_41 : radical 41 = 41 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_42 : radical 42 = 42 := by
  have h1 : 42 = 2 * 21 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_21]
  try rfl
theorem radical_43 : radical 43 = 43 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_44 : radical 44 = 22 := by
  have h1 : 44 = 4 * 11 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_11]
  try rfl
theorem radical_45 : radical 45 = 15 := by
  have h1 : 45 = 9 * 5 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_9, radical_5]
  try rfl
theorem radical_46 : radical 46 = 46 := by
  have h1 : 46 = 2 * 23 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_23]
  try rfl
theorem radical_47 : radical 47 = 47 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_48 : radical 48 = 6 := by
  have h1 : 48 = 16 * 3 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_16, radical_3]
  try rfl
theorem radical_49 : radical 49 = 7 := by
  have h1 : 49 = 7 ^ 2 := by norm_num
  rw [h1]
  rw [radical_pow]
  · rw [radical_7]
  · decide
theorem radical_50 : radical 50 = 10 := by
  have h1 : 50 = 2 * 25 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_25]
  try rfl
theorem radical_51 : radical 51 = 51 := by
  have h1 : 51 = 3 * 17 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_17]
  try rfl
theorem radical_52 : radical 52 = 26 := by
  have h1 : 52 = 4 * 13 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_13]
  try rfl
theorem radical_53 : radical 53 = 53 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_54 : radical 54 = 6 := by
  have h1 : 54 = 2 * 27 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_27]
  try rfl
theorem radical_55 : radical 55 = 55 := by
  have h1 : 55 = 5 * 11 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_5, radical_11]
  try rfl
theorem radical_56 : radical 56 = 14 := by
  have h1 : 56 = 8 * 7 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_8, radical_7]
  try rfl
theorem radical_57 : radical 57 = 57 := by
  have h1 : 57 = 3 * 19 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_3, radical_19]
  try rfl
theorem radical_58 : radical 58 = 58 := by
  have h1 : 58 = 2 * 29 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_2, radical_29]
  try rfl
theorem radical_59 : radical 59 = 59 := by rw [radical_of_prime (Nat.Prime.prime (by decide))]; rfl
theorem radical_60 : radical 60 = 30 := by
  have h1 : 60 = 4 * 15 := by norm_num
  rw [h1]
  rw [radical_mul (by rw [← Nat.coprime_iff_isRelPrime]; decide)]
  rw [radical_4, radical_15]
  try rfl

theorem A195441_val_0 : A195441 (1 - 1) = 1 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 1 - 0 = 1 := rfl
  have hc0 : Nat.choose 1 0 = 1 := rfl
  have hs1 : 1 - 1 = 0 := rfl
  have hc1 : Nat.choose 1 1 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_1 : A195441 (2 - 1) = 1 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 2 - 0 = 2 := rfl
  have hc0 : Nat.choose 2 0 = 1 := rfl
  have hs1 : 2 - 1 = 1 := rfl
  have hc1 : Nat.choose 2 1 = 2 := rfl
  have hs2 : 2 - 2 = 0 := rfl
  have hc2 : Nat.choose 2 2 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_2 : A195441 (3 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 3 - 0 = 3 := rfl
  have hc0 : Nat.choose 3 0 = 1 := rfl
  have hs1 : 3 - 1 = 2 := rfl
  have hc1 : Nat.choose 3 1 = 3 := rfl
  have hs2 : 3 - 2 = 1 := rfl
  have hc2 : Nat.choose 3 2 = 3 := rfl
  have hs3 : 3 - 3 = 0 := rfl
  have hc3 : Nat.choose 3 3 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_3 : A195441 (4 - 1) = 1 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 4 - 0 = 4 := rfl
  have hc0 : Nat.choose 4 0 = 1 := rfl
  have hs1 : 4 - 1 = 3 := rfl
  have hc1 : Nat.choose 4 1 = 4 := rfl
  have hs2 : 4 - 2 = 2 := rfl
  have hc2 : Nat.choose 4 2 = 6 := rfl
  have hs3 : 4 - 3 = 1 := rfl
  have hc3 : Nat.choose 4 3 = 4 := rfl
  have hs4 : 4 - 4 = 0 := rfl
  have hc4 : Nat.choose 4 4 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_4 : A195441 (5 - 1) = 6 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 5 - 0 = 5 := rfl
  have hc0 : Nat.choose 5 0 = 1 := rfl
  have hs1 : 5 - 1 = 4 := rfl
  have hc1 : Nat.choose 5 1 = 5 := rfl
  have hs2 : 5 - 2 = 3 := rfl
  have hc2 : Nat.choose 5 2 = 10 := rfl
  have hs3 : 5 - 3 = 2 := rfl
  have hc3 : Nat.choose 5 3 = 10 := rfl
  have hs4 : 5 - 4 = 1 := rfl
  have hc4 : Nat.choose 5 4 = 5 := rfl
  have hs5 : 5 - 5 = 0 := rfl
  have hc5 : Nat.choose 5 5 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_5 : A195441 (6 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 6 - 0 = 6 := rfl
  have hc0 : Nat.choose 6 0 = 1 := rfl
  have hs1 : 6 - 1 = 5 := rfl
  have hc1 : Nat.choose 6 1 = 6 := rfl
  have hs2 : 6 - 2 = 4 := rfl
  have hc2 : Nat.choose 6 2 = 15 := rfl
  have hs3 : 6 - 3 = 3 := rfl
  have hc3 : Nat.choose 6 3 = 20 := rfl
  have hs4 : 6 - 4 = 2 := rfl
  have hc4 : Nat.choose 6 4 = 15 := rfl
  have hs5 : 6 - 5 = 1 := rfl
  have hc5 : Nat.choose 6 5 = 6 := rfl
  have hs6 : 6 - 6 = 0 := rfl
  have hc6 : Nat.choose 6 6 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_6 : A195441 (7 - 1) = 6 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 7 - 0 = 7 := rfl
  have hc0 : Nat.choose 7 0 = 1 := rfl
  have hs1 : 7 - 1 = 6 := rfl
  have hc1 : Nat.choose 7 1 = 7 := rfl
  have hs2 : 7 - 2 = 5 := rfl
  have hc2 : Nat.choose 7 2 = 21 := rfl
  have hs3 : 7 - 3 = 4 := rfl
  have hc3 : Nat.choose 7 3 = 35 := rfl
  have hs4 : 7 - 4 = 3 := rfl
  have hc4 : Nat.choose 7 4 = 35 := rfl
  have hs5 : 7 - 5 = 2 := rfl
  have hc5 : Nat.choose 7 5 = 21 := rfl
  have hs6 : 7 - 6 = 1 := rfl
  have hc6 : Nat.choose 7 6 = 7 := rfl
  have hs7 : 7 - 7 = 0 := rfl
  have hc7 : Nat.choose 7 7 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_7 : A195441 (8 - 1) = 3 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 8 - 0 = 8 := rfl
  have hc0 : Nat.choose 8 0 = 1 := rfl
  have hs1 : 8 - 1 = 7 := rfl
  have hc1 : Nat.choose 8 1 = 8 := rfl
  have hs2 : 8 - 2 = 6 := rfl
  have hc2 : Nat.choose 8 2 = 28 := rfl
  have hs3 : 8 - 3 = 5 := rfl
  have hc3 : Nat.choose 8 3 = 56 := rfl
  have hs4 : 8 - 4 = 4 := rfl
  have hc4 : Nat.choose 8 4 = 70 := rfl
  have hs5 : 8 - 5 = 3 := rfl
  have hc5 : Nat.choose 8 5 = 56 := rfl
  have hs6 : 8 - 6 = 2 := rfl
  have hc6 : Nat.choose 8 6 = 28 := rfl
  have hs7 : 8 - 7 = 1 := rfl
  have hc7 : Nat.choose 8 7 = 8 := rfl
  have hs8 : 8 - 8 = 0 := rfl
  have hc8 : Nat.choose 8 8 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_8 : A195441 (9 - 1) = 10 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 9 - 0 = 9 := rfl
  have hc0 : Nat.choose 9 0 = 1 := rfl
  have hs1 : 9 - 1 = 8 := rfl
  have hc1 : Nat.choose 9 1 = 9 := rfl
  have hs2 : 9 - 2 = 7 := rfl
  have hc2 : Nat.choose 9 2 = 36 := rfl
  have hs3 : 9 - 3 = 6 := rfl
  have hc3 : Nat.choose 9 3 = 84 := rfl
  have hs4 : 9 - 4 = 5 := rfl
  have hc4 : Nat.choose 9 4 = 126 := rfl
  have hs5 : 9 - 5 = 4 := rfl
  have hc5 : Nat.choose 9 5 = 126 := rfl
  have hs6 : 9 - 6 = 3 := rfl
  have hc6 : Nat.choose 9 6 = 84 := rfl
  have hs7 : 9 - 7 = 2 := rfl
  have hc7 : Nat.choose 9 7 = 36 := rfl
  have hs8 : 9 - 8 = 1 := rfl
  have hc8 : Nat.choose 9 8 = 9 := rfl
  have hs9 : 9 - 9 = 0 := rfl
  have hc9 : Nat.choose 9 9 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_9 : A195441 (10 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 10 - 0 = 10 := rfl
  have hc0 : Nat.choose 10 0 = 1 := rfl
  have hs1 : 10 - 1 = 9 := rfl
  have hc1 : Nat.choose 10 1 = 10 := rfl
  have hs2 : 10 - 2 = 8 := rfl
  have hc2 : Nat.choose 10 2 = 45 := rfl
  have hs3 : 10 - 3 = 7 := rfl
  have hc3 : Nat.choose 10 3 = 120 := rfl
  have hs4 : 10 - 4 = 6 := rfl
  have hc4 : Nat.choose 10 4 = 210 := rfl
  have hs5 : 10 - 5 = 5 := rfl
  have hc5 : Nat.choose 10 5 = 252 := rfl
  have hs6 : 10 - 6 = 4 := rfl
  have hc6 : Nat.choose 10 6 = 210 := rfl
  have hs7 : 10 - 7 = 3 := rfl
  have hc7 : Nat.choose 10 7 = 120 := rfl
  have hs8 : 10 - 8 = 2 := rfl
  have hc8 : Nat.choose 10 8 = 45 := rfl
  have hs9 : 10 - 9 = 1 := rfl
  have hc9 : Nat.choose 10 9 = 10 := rfl
  have hs10 : 10 - 10 = 0 := rfl
  have hc10 : Nat.choose 10 10 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_10 : A195441 (11 - 1) = 6 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 11 - 0 = 11 := rfl
  have hc0 : Nat.choose 11 0 = 1 := rfl
  have hs1 : 11 - 1 = 10 := rfl
  have hc1 : Nat.choose 11 1 = 11 := rfl
  have hs2 : 11 - 2 = 9 := rfl
  have hc2 : Nat.choose 11 2 = 55 := rfl
  have hs3 : 11 - 3 = 8 := rfl
  have hc3 : Nat.choose 11 3 = 165 := rfl
  have hs4 : 11 - 4 = 7 := rfl
  have hc4 : Nat.choose 11 4 = 330 := rfl
  have hs5 : 11 - 5 = 6 := rfl
  have hc5 : Nat.choose 11 5 = 462 := rfl
  have hs6 : 11 - 6 = 5 := rfl
  have hc6 : Nat.choose 11 6 = 462 := rfl
  have hs7 : 11 - 7 = 4 := rfl
  have hc7 : Nat.choose 11 7 = 330 := rfl
  have hs8 : 11 - 8 = 3 := rfl
  have hc8 : Nat.choose 11 8 = 165 := rfl
  have hs9 : 11 - 9 = 2 := rfl
  have hc9 : Nat.choose 11 9 = 55 := rfl
  have hs10 : 11 - 10 = 1 := rfl
  have hc10 : Nat.choose 11 10 = 11 := rfl
  have hs11 : 11 - 11 = 0 := rfl
  have hc11 : Nat.choose 11 11 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_11 : A195441 (12 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 12 - 0 = 12 := rfl
  have hc0 : Nat.choose 12 0 = 1 := rfl
  have hs1 : 12 - 1 = 11 := rfl
  have hc1 : Nat.choose 12 1 = 12 := rfl
  have hs2 : 12 - 2 = 10 := rfl
  have hc2 : Nat.choose 12 2 = 66 := rfl
  have hs3 : 12 - 3 = 9 := rfl
  have hc3 : Nat.choose 12 3 = 220 := rfl
  have hs4 : 12 - 4 = 8 := rfl
  have hc4 : Nat.choose 12 4 = 495 := rfl
  have hs5 : 12 - 5 = 7 := rfl
  have hc5 : Nat.choose 12 5 = 792 := rfl
  have hs6 : 12 - 6 = 6 := rfl
  have hc6 : Nat.choose 12 6 = 924 := rfl
  have hs7 : 12 - 7 = 5 := rfl
  have hc7 : Nat.choose 12 7 = 792 := rfl
  have hs8 : 12 - 8 = 4 := rfl
  have hc8 : Nat.choose 12 8 = 495 := rfl
  have hs9 : 12 - 9 = 3 := rfl
  have hc9 : Nat.choose 12 9 = 220 := rfl
  have hs10 : 12 - 10 = 2 := rfl
  have hc10 : Nat.choose 12 10 = 66 := rfl
  have hs11 : 12 - 11 = 1 := rfl
  have hc11 : Nat.choose 12 11 = 12 := rfl
  have hs12 : 12 - 12 = 0 := rfl
  have hc12 : Nat.choose 12 12 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_12 : A195441 (13 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 13 - 0 = 13 := rfl
  have hc0 : Nat.choose 13 0 = 1 := rfl
  have hs1 : 13 - 1 = 12 := rfl
  have hc1 : Nat.choose 13 1 = 13 := rfl
  have hs2 : 13 - 2 = 11 := rfl
  have hc2 : Nat.choose 13 2 = 78 := rfl
  have hs3 : 13 - 3 = 10 := rfl
  have hc3 : Nat.choose 13 3 = 286 := rfl
  have hs4 : 13 - 4 = 9 := rfl
  have hc4 : Nat.choose 13 4 = 715 := rfl
  have hs5 : 13 - 5 = 8 := rfl
  have hc5 : Nat.choose 13 5 = 1287 := rfl
  have hs6 : 13 - 6 = 7 := rfl
  have hc6 : Nat.choose 13 6 = 1716 := rfl
  have hs7 : 13 - 7 = 6 := rfl
  have hc7 : Nat.choose 13 7 = 1716 := rfl
  have hs8 : 13 - 8 = 5 := rfl
  have hc8 : Nat.choose 13 8 = 1287 := rfl
  have hs9 : 13 - 9 = 4 := rfl
  have hc9 : Nat.choose 13 9 = 715 := rfl
  have hs10 : 13 - 10 = 3 := rfl
  have hc10 : Nat.choose 13 10 = 286 := rfl
  have hs11 : 13 - 11 = 2 := rfl
  have hc11 : Nat.choose 13 11 = 78 := rfl
  have hs12 : 13 - 12 = 1 := rfl
  have hc12 : Nat.choose 13 12 = 13 := rfl
  have hs13 : 13 - 13 = 0 := rfl
  have hc13 : Nat.choose 13 13 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_13 : A195441 (14 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 14 - 0 = 14 := rfl
  have hc0 : Nat.choose 14 0 = 1 := rfl
  have hs1 : 14 - 1 = 13 := rfl
  have hc1 : Nat.choose 14 1 = 14 := rfl
  have hs2 : 14 - 2 = 12 := rfl
  have hc2 : Nat.choose 14 2 = 91 := rfl
  have hs3 : 14 - 3 = 11 := rfl
  have hc3 : Nat.choose 14 3 = 364 := rfl
  have hs4 : 14 - 4 = 10 := rfl
  have hc4 : Nat.choose 14 4 = 1001 := rfl
  have hs5 : 14 - 5 = 9 := rfl
  have hc5 : Nat.choose 14 5 = 2002 := rfl
  have hs6 : 14 - 6 = 8 := rfl
  have hc6 : Nat.choose 14 6 = 3003 := rfl
  have hs7 : 14 - 7 = 7 := rfl
  have hc7 : Nat.choose 14 7 = 3432 := rfl
  have hs8 : 14 - 8 = 6 := rfl
  have hc8 : Nat.choose 14 8 = 3003 := rfl
  have hs9 : 14 - 9 = 5 := rfl
  have hc9 : Nat.choose 14 9 = 2002 := rfl
  have hs10 : 14 - 10 = 4 := rfl
  have hc10 : Nat.choose 14 10 = 1001 := rfl
  have hs11 : 14 - 11 = 3 := rfl
  have hc11 : Nat.choose 14 11 = 364 := rfl
  have hs12 : 14 - 12 = 2 := rfl
  have hc12 : Nat.choose 14 12 = 91 := rfl
  have hs13 : 14 - 13 = 1 := rfl
  have hc13 : Nat.choose 14 13 = 14 := rfl
  have hs14 : 14 - 14 = 0 := rfl
  have hc14 : Nat.choose 14 14 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_14 : A195441 (15 - 1) = 6 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 15 - 0 = 15 := rfl
  have hc0 : Nat.choose 15 0 = 1 := rfl
  have hs1 : 15 - 1 = 14 := rfl
  have hc1 : Nat.choose 15 1 = 15 := rfl
  have hs2 : 15 - 2 = 13 := rfl
  have hc2 : Nat.choose 15 2 = 105 := rfl
  have hs3 : 15 - 3 = 12 := rfl
  have hc3 : Nat.choose 15 3 = 455 := rfl
  have hs4 : 15 - 4 = 11 := rfl
  have hc4 : Nat.choose 15 4 = 1365 := rfl
  have hs5 : 15 - 5 = 10 := rfl
  have hc5 : Nat.choose 15 5 = 3003 := rfl
  have hs6 : 15 - 6 = 9 := rfl
  have hc6 : Nat.choose 15 6 = 5005 := rfl
  have hs7 : 15 - 7 = 8 := rfl
  have hc7 : Nat.choose 15 7 = 6435 := rfl
  have hs8 : 15 - 8 = 7 := rfl
  have hc8 : Nat.choose 15 8 = 6435 := rfl
  have hs9 : 15 - 9 = 6 := rfl
  have hc9 : Nat.choose 15 9 = 5005 := rfl
  have hs10 : 15 - 10 = 5 := rfl
  have hc10 : Nat.choose 15 10 = 3003 := rfl
  have hs11 : 15 - 11 = 4 := rfl
  have hc11 : Nat.choose 15 11 = 1365 := rfl
  have hs12 : 15 - 12 = 3 := rfl
  have hc12 : Nat.choose 15 12 = 455 := rfl
  have hs13 : 15 - 13 = 2 := rfl
  have hc13 : Nat.choose 15 13 = 105 := rfl
  have hs14 : 15 - 14 = 1 := rfl
  have hc14 : Nat.choose 15 14 = 15 := rfl
  have hs15 : 15 - 15 = 0 := rfl
  have hc15 : Nat.choose 15 15 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_15 : A195441 (16 - 1) = 3 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 16 - 0 = 16 := rfl
  have hc0 : Nat.choose 16 0 = 1 := rfl
  have hs1 : 16 - 1 = 15 := rfl
  have hc1 : Nat.choose 16 1 = 16 := rfl
  have hs2 : 16 - 2 = 14 := rfl
  have hc2 : Nat.choose 16 2 = 120 := rfl
  have hs3 : 16 - 3 = 13 := rfl
  have hc3 : Nat.choose 16 3 = 560 := rfl
  have hs4 : 16 - 4 = 12 := rfl
  have hc4 : Nat.choose 16 4 = 1820 := rfl
  have hs5 : 16 - 5 = 11 := rfl
  have hc5 : Nat.choose 16 5 = 4368 := rfl
  have hs6 : 16 - 6 = 10 := rfl
  have hc6 : Nat.choose 16 6 = 8008 := rfl
  have hs7 : 16 - 7 = 9 := rfl
  have hc7 : Nat.choose 16 7 = 11440 := rfl
  have hs8 : 16 - 8 = 8 := rfl
  have hc8 : Nat.choose 16 8 = 12870 := rfl
  have hs9 : 16 - 9 = 7 := rfl
  have hc9 : Nat.choose 16 9 = 11440 := rfl
  have hs10 : 16 - 10 = 6 := rfl
  have hc10 : Nat.choose 16 10 = 8008 := rfl
  have hs11 : 16 - 11 = 5 := rfl
  have hc11 : Nat.choose 16 11 = 4368 := rfl
  have hs12 : 16 - 12 = 4 := rfl
  have hc12 : Nat.choose 16 12 = 1820 := rfl
  have hs13 : 16 - 13 = 3 := rfl
  have hc13 : Nat.choose 16 13 = 560 := rfl
  have hs14 : 16 - 14 = 2 := rfl
  have hc14 : Nat.choose 16 14 = 120 := rfl
  have hs15 : 16 - 15 = 1 := rfl
  have hc15 : Nat.choose 16 15 = 16 := rfl
  have hs16 : 16 - 16 = 0 := rfl
  have hc16 : Nat.choose 16 16 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_16 : A195441 (17 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 17 - 0 = 17 := rfl
  have hc0 : Nat.choose 17 0 = 1 := rfl
  have hs1 : 17 - 1 = 16 := rfl
  have hc1 : Nat.choose 17 1 = 17 := rfl
  have hs2 : 17 - 2 = 15 := rfl
  have hc2 : Nat.choose 17 2 = 136 := rfl
  have hs3 : 17 - 3 = 14 := rfl
  have hc3 : Nat.choose 17 3 = 680 := rfl
  have hs4 : 17 - 4 = 13 := rfl
  have hc4 : Nat.choose 17 4 = 2380 := rfl
  have hs5 : 17 - 5 = 12 := rfl
  have hc5 : Nat.choose 17 5 = 6188 := rfl
  have hs6 : 17 - 6 = 11 := rfl
  have hc6 : Nat.choose 17 6 = 12376 := rfl
  have hs7 : 17 - 7 = 10 := rfl
  have hc7 : Nat.choose 17 7 = 19448 := rfl
  have hs8 : 17 - 8 = 9 := rfl
  have hc8 : Nat.choose 17 8 = 24310 := rfl
  have hs9 : 17 - 9 = 8 := rfl
  have hc9 : Nat.choose 17 9 = 24310 := rfl
  have hs10 : 17 - 10 = 7 := rfl
  have hc10 : Nat.choose 17 10 = 19448 := rfl
  have hs11 : 17 - 11 = 6 := rfl
  have hc11 : Nat.choose 17 11 = 12376 := rfl
  have hs12 : 17 - 12 = 5 := rfl
  have hc12 : Nat.choose 17 12 = 6188 := rfl
  have hs13 : 17 - 13 = 4 := rfl
  have hc13 : Nat.choose 17 13 = 2380 := rfl
  have hs14 : 17 - 14 = 3 := rfl
  have hc14 : Nat.choose 17 14 = 680 := rfl
  have hs15 : 17 - 15 = 2 := rfl
  have hc15 : Nat.choose 17 15 = 136 := rfl
  have hs16 : 17 - 16 = 1 := rfl
  have hc16 : Nat.choose 17 16 = 17 := rfl
  have hs17 : 17 - 17 = 0 := rfl
  have hc17 : Nat.choose 17 17 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_17 : A195441 (18 - 1) = 10 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 18 - 0 = 18 := rfl
  have hc0 : Nat.choose 18 0 = 1 := rfl
  have hs1 : 18 - 1 = 17 := rfl
  have hc1 : Nat.choose 18 1 = 18 := rfl
  have hs2 : 18 - 2 = 16 := rfl
  have hc2 : Nat.choose 18 2 = 153 := rfl
  have hs3 : 18 - 3 = 15 := rfl
  have hc3 : Nat.choose 18 3 = 816 := rfl
  have hs4 : 18 - 4 = 14 := rfl
  have hc4 : Nat.choose 18 4 = 3060 := rfl
  have hs5 : 18 - 5 = 13 := rfl
  have hc5 : Nat.choose 18 5 = 8568 := rfl
  have hs6 : 18 - 6 = 12 := rfl
  have hc6 : Nat.choose 18 6 = 18564 := rfl
  have hs7 : 18 - 7 = 11 := rfl
  have hc7 : Nat.choose 18 7 = 31824 := rfl
  have hs8 : 18 - 8 = 10 := rfl
  have hc8 : Nat.choose 18 8 = 43758 := rfl
  have hs9 : 18 - 9 = 9 := rfl
  have hc9 : Nat.choose 18 9 = 48620 := rfl
  have hs10 : 18 - 10 = 8 := rfl
  have hc10 : Nat.choose 18 10 = 43758 := rfl
  have hs11 : 18 - 11 = 7 := rfl
  have hc11 : Nat.choose 18 11 = 31824 := rfl
  have hs12 : 18 - 12 = 6 := rfl
  have hc12 : Nat.choose 18 12 = 18564 := rfl
  have hs13 : 18 - 13 = 5 := rfl
  have hc13 : Nat.choose 18 13 = 8568 := rfl
  have hs14 : 18 - 14 = 4 := rfl
  have hc14 : Nat.choose 18 14 = 3060 := rfl
  have hs15 : 18 - 15 = 3 := rfl
  have hc15 : Nat.choose 18 15 = 816 := rfl
  have hs16 : 18 - 16 = 2 := rfl
  have hc16 : Nat.choose 18 16 = 153 := rfl
  have hs17 : 18 - 17 = 1 := rfl
  have hc17 : Nat.choose 18 17 = 18 := rfl
  have hs18 : 18 - 18 = 0 := rfl
  have hc18 : Nat.choose 18 18 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_18 : A195441 (19 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 19 - 0 = 19 := rfl
  have hc0 : Nat.choose 19 0 = 1 := rfl
  have hs1 : 19 - 1 = 18 := rfl
  have hc1 : Nat.choose 19 1 = 19 := rfl
  have hs2 : 19 - 2 = 17 := rfl
  have hc2 : Nat.choose 19 2 = 171 := rfl
  have hs3 : 19 - 3 = 16 := rfl
  have hc3 : Nat.choose 19 3 = 969 := rfl
  have hs4 : 19 - 4 = 15 := rfl
  have hc4 : Nat.choose 19 4 = 3876 := rfl
  have hs5 : 19 - 5 = 14 := rfl
  have hc5 : Nat.choose 19 5 = 11628 := rfl
  have hs6 : 19 - 6 = 13 := rfl
  have hc6 : Nat.choose 19 6 = 27132 := rfl
  have hs7 : 19 - 7 = 12 := rfl
  have hc7 : Nat.choose 19 7 = 50388 := rfl
  have hs8 : 19 - 8 = 11 := rfl
  have hc8 : Nat.choose 19 8 = 75582 := rfl
  have hs9 : 19 - 9 = 10 := rfl
  have hc9 : Nat.choose 19 9 = 92378 := rfl
  have hs10 : 19 - 10 = 9 := rfl
  have hc10 : Nat.choose 19 10 = 92378 := rfl
  have hs11 : 19 - 11 = 8 := rfl
  have hc11 : Nat.choose 19 11 = 75582 := rfl
  have hs12 : 19 - 12 = 7 := rfl
  have hc12 : Nat.choose 19 12 = 50388 := rfl
  have hs13 : 19 - 13 = 6 := rfl
  have hc13 : Nat.choose 19 13 = 27132 := rfl
  have hs14 : 19 - 14 = 5 := rfl
  have hc14 : Nat.choose 19 14 = 11628 := rfl
  have hs15 : 19 - 15 = 4 := rfl
  have hc15 : Nat.choose 19 15 = 3876 := rfl
  have hs16 : 19 - 16 = 3 := rfl
  have hc16 : Nat.choose 19 16 = 969 := rfl
  have hs17 : 19 - 17 = 2 := rfl
  have hc17 : Nat.choose 19 17 = 171 := rfl
  have hs18 : 19 - 18 = 1 := rfl
  have hc18 : Nat.choose 19 18 = 19 := rfl
  have hs19 : 19 - 19 = 0 := rfl
  have hc19 : Nat.choose 19 19 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_19 : A195441 (20 - 1) = 42 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 20 - 0 = 20 := rfl
  have hc0 : Nat.choose 20 0 = 1 := rfl
  have hs1 : 20 - 1 = 19 := rfl
  have hc1 : Nat.choose 20 1 = 20 := rfl
  have hs2 : 20 - 2 = 18 := rfl
  have hc2 : Nat.choose 20 2 = 190 := rfl
  have hs3 : 20 - 3 = 17 := rfl
  have hc3 : Nat.choose 20 3 = 1140 := rfl
  have hs4 : 20 - 4 = 16 := rfl
  have hc4 : Nat.choose 20 4 = 4845 := rfl
  have hs5 : 20 - 5 = 15 := rfl
  have hc5 : Nat.choose 20 5 = 15504 := rfl
  have hs6 : 20 - 6 = 14 := rfl
  have hc6 : Nat.choose 20 6 = 38760 := rfl
  have hs7 : 20 - 7 = 13 := rfl
  have hc7 : Nat.choose 20 7 = 77520 := rfl
  have hs8 : 20 - 8 = 12 := rfl
  have hc8 : Nat.choose 20 8 = 125970 := rfl
  have hs9 : 20 - 9 = 11 := rfl
  have hc9 : Nat.choose 20 9 = 167960 := rfl
  have hs10 : 20 - 10 = 10 := rfl
  have hc10 : Nat.choose 20 10 = 184756 := rfl
  have hs11 : 20 - 11 = 9 := rfl
  have hc11 : Nat.choose 20 11 = 167960 := rfl
  have hs12 : 20 - 12 = 8 := rfl
  have hc12 : Nat.choose 20 12 = 125970 := rfl
  have hs13 : 20 - 13 = 7 := rfl
  have hc13 : Nat.choose 20 13 = 77520 := rfl
  have hs14 : 20 - 14 = 6 := rfl
  have hc14 : Nat.choose 20 14 = 38760 := rfl
  have hs15 : 20 - 15 = 5 := rfl
  have hc15 : Nat.choose 20 15 = 15504 := rfl
  have hs16 : 20 - 16 = 4 := rfl
  have hc16 : Nat.choose 20 16 = 4845 := rfl
  have hs17 : 20 - 17 = 3 := rfl
  have hc17 : Nat.choose 20 17 = 1140 := rfl
  have hs18 : 20 - 18 = 2 := rfl
  have hc18 : Nat.choose 20 18 = 190 := rfl
  have hs19 : 20 - 19 = 1 := rfl
  have hc19 : Nat.choose 20 19 = 20 := rfl
  have hs20 : 20 - 20 = 0 := rfl
  have hc20 : Nat.choose 20 20 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_20 : A195441 (21 - 1) = 330 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 21 - 0 = 21 := rfl
  have hc0 : Nat.choose 21 0 = 1 := rfl
  have hs1 : 21 - 1 = 20 := rfl
  have hc1 : Nat.choose 21 1 = 21 := rfl
  have hs2 : 21 - 2 = 19 := rfl
  have hc2 : Nat.choose 21 2 = 210 := rfl
  have hs3 : 21 - 3 = 18 := rfl
  have hc3 : Nat.choose 21 3 = 1330 := rfl
  have hs4 : 21 - 4 = 17 := rfl
  have hc4 : Nat.choose 21 4 = 5985 := rfl
  have hs5 : 21 - 5 = 16 := rfl
  have hc5 : Nat.choose 21 5 = 20349 := rfl
  have hs6 : 21 - 6 = 15 := rfl
  have hc6 : Nat.choose 21 6 = 54264 := rfl
  have hs7 : 21 - 7 = 14 := rfl
  have hc7 : Nat.choose 21 7 = 116280 := rfl
  have hs8 : 21 - 8 = 13 := rfl
  have hc8 : Nat.choose 21 8 = 203490 := rfl
  have hs9 : 21 - 9 = 12 := rfl
  have hc9 : Nat.choose 21 9 = 293930 := rfl
  have hs10 : 21 - 10 = 11 := rfl
  have hc10 : Nat.choose 21 10 = 352716 := rfl
  have hs11 : 21 - 11 = 10 := rfl
  have hc11 : Nat.choose 21 11 = 352716 := rfl
  have hs12 : 21 - 12 = 9 := rfl
  have hc12 : Nat.choose 21 12 = 293930 := rfl
  have hs13 : 21 - 13 = 8 := rfl
  have hc13 : Nat.choose 21 13 = 203490 := rfl
  have hs14 : 21 - 14 = 7 := rfl
  have hc14 : Nat.choose 21 14 = 116280 := rfl
  have hs15 : 21 - 15 = 6 := rfl
  have hc15 : Nat.choose 21 15 = 54264 := rfl
  have hs16 : 21 - 16 = 5 := rfl
  have hc16 : Nat.choose 21 16 = 20349 := rfl
  have hs17 : 21 - 17 = 4 := rfl
  have hc17 : Nat.choose 21 17 = 5985 := rfl
  have hs18 : 21 - 18 = 3 := rfl
  have hc18 : Nat.choose 21 18 = 1330 := rfl
  have hs19 : 21 - 19 = 2 := rfl
  have hc19 : Nat.choose 21 19 = 210 := rfl
  have hs20 : 21 - 20 = 1 := rfl
  have hc20 : Nat.choose 21 20 = 21 := rfl
  have hs21 : 21 - 21 = 0 := rfl
  have hc21 : Nat.choose 21 21 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_21 : A195441 (22 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 22 - 0 = 22 := rfl
  have hc0 : Nat.choose 22 0 = 1 := rfl
  have hs1 : 22 - 1 = 21 := rfl
  have hc1 : Nat.choose 22 1 = 22 := rfl
  have hs2 : 22 - 2 = 20 := rfl
  have hc2 : Nat.choose 22 2 = 231 := rfl
  have hs3 : 22 - 3 = 19 := rfl
  have hc3 : Nat.choose 22 3 = 1540 := rfl
  have hs4 : 22 - 4 = 18 := rfl
  have hc4 : Nat.choose 22 4 = 7315 := rfl
  have hs5 : 22 - 5 = 17 := rfl
  have hc5 : Nat.choose 22 5 = 26334 := rfl
  have hs6 : 22 - 6 = 16 := rfl
  have hc6 : Nat.choose 22 6 = 74613 := rfl
  have hs7 : 22 - 7 = 15 := rfl
  have hc7 : Nat.choose 22 7 = 170544 := rfl
  have hs8 : 22 - 8 = 14 := rfl
  have hc8 : Nat.choose 22 8 = 319770 := rfl
  have hs9 : 22 - 9 = 13 := rfl
  have hc9 : Nat.choose 22 9 = 497420 := rfl
  have hs10 : 22 - 10 = 12 := rfl
  have hc10 : Nat.choose 22 10 = 646646 := rfl
  have hs11 : 22 - 11 = 11 := rfl
  have hc11 : Nat.choose 22 11 = 705432 := rfl
  have hs12 : 22 - 12 = 10 := rfl
  have hc12 : Nat.choose 22 12 = 646646 := rfl
  have hs13 : 22 - 13 = 9 := rfl
  have hc13 : Nat.choose 22 13 = 497420 := rfl
  have hs14 : 22 - 14 = 8 := rfl
  have hc14 : Nat.choose 22 14 = 319770 := rfl
  have hs15 : 22 - 15 = 7 := rfl
  have hc15 : Nat.choose 22 15 = 170544 := rfl
  have hs16 : 22 - 16 = 6 := rfl
  have hc16 : Nat.choose 22 16 = 74613 := rfl
  have hs17 : 22 - 17 = 5 := rfl
  have hc17 : Nat.choose 22 17 = 26334 := rfl
  have hs18 : 22 - 18 = 4 := rfl
  have hc18 : Nat.choose 22 18 = 7315 := rfl
  have hs19 : 22 - 19 = 3 := rfl
  have hc19 : Nat.choose 22 19 = 1540 := rfl
  have hs20 : 22 - 20 = 2 := rfl
  have hc20 : Nat.choose 22 20 = 231 := rfl
  have hs21 : 22 - 21 = 1 := rfl
  have hc21 : Nat.choose 22 21 = 22 := rfl
  have hs22 : 22 - 22 = 0 := rfl
  have hc22 : Nat.choose 22 22 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_22 : A195441 (23 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 23 - 0 = 23 := rfl
  have hc0 : Nat.choose 23 0 = 1 := rfl
  have hs1 : 23 - 1 = 22 := rfl
  have hc1 : Nat.choose 23 1 = 23 := rfl
  have hs2 : 23 - 2 = 21 := rfl
  have hc2 : Nat.choose 23 2 = 253 := rfl
  have hs3 : 23 - 3 = 20 := rfl
  have hc3 : Nat.choose 23 3 = 1771 := rfl
  have hs4 : 23 - 4 = 19 := rfl
  have hc4 : Nat.choose 23 4 = 8855 := rfl
  have hs5 : 23 - 5 = 18 := rfl
  have hc5 : Nat.choose 23 5 = 33649 := rfl
  have hs6 : 23 - 6 = 17 := rfl
  have hc6 : Nat.choose 23 6 = 100947 := rfl
  have hs7 : 23 - 7 = 16 := rfl
  have hc7 : Nat.choose 23 7 = 245157 := rfl
  have hs8 : 23 - 8 = 15 := rfl
  have hc8 : Nat.choose 23 8 = 490314 := rfl
  have hs9 : 23 - 9 = 14 := rfl
  have hc9 : Nat.choose 23 9 = 817190 := rfl
  have hs10 : 23 - 10 = 13 := rfl
  have hc10 : Nat.choose 23 10 = 1144066 := rfl
  have hs11 : 23 - 11 = 12 := rfl
  have hc11 : Nat.choose 23 11 = 1352078 := rfl
  have hs12 : 23 - 12 = 11 := rfl
  have hc12 : Nat.choose 23 12 = 1352078 := rfl
  have hs13 : 23 - 13 = 10 := rfl
  have hc13 : Nat.choose 23 13 = 1144066 := rfl
  have hs14 : 23 - 14 = 9 := rfl
  have hc14 : Nat.choose 23 14 = 817190 := rfl
  have hs15 : 23 - 15 = 8 := rfl
  have hc15 : Nat.choose 23 15 = 490314 := rfl
  have hs16 : 23 - 16 = 7 := rfl
  have hc16 : Nat.choose 23 16 = 245157 := rfl
  have hs17 : 23 - 17 = 6 := rfl
  have hc17 : Nat.choose 23 17 = 100947 := rfl
  have hs18 : 23 - 18 = 5 := rfl
  have hc18 : Nat.choose 23 18 = 33649 := rfl
  have hs19 : 23 - 19 = 4 := rfl
  have hc19 : Nat.choose 23 19 = 8855 := rfl
  have hs20 : 23 - 20 = 3 := rfl
  have hc20 : Nat.choose 23 20 = 1771 := rfl
  have hs21 : 23 - 21 = 2 := rfl
  have hc21 : Nat.choose 23 21 = 253 := rfl
  have hs22 : 23 - 22 = 1 := rfl
  have hc22 : Nat.choose 23 22 = 23 := rfl
  have hs23 : 23 - 23 = 0 := rfl
  have hc23 : Nat.choose 23 23 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_23 : A195441 (24 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 24 - 0 = 24 := rfl
  have hc0 : Nat.choose 24 0 = 1 := rfl
  have hs1 : 24 - 1 = 23 := rfl
  have hc1 : Nat.choose 24 1 = 24 := rfl
  have hs2 : 24 - 2 = 22 := rfl
  have hc2 : Nat.choose 24 2 = 276 := rfl
  have hs3 : 24 - 3 = 21 := rfl
  have hc3 : Nat.choose 24 3 = 2024 := rfl
  have hs4 : 24 - 4 = 20 := rfl
  have hc4 : Nat.choose 24 4 = 10626 := rfl
  have hs5 : 24 - 5 = 19 := rfl
  have hc5 : Nat.choose 24 5 = 42504 := rfl
  have hs6 : 24 - 6 = 18 := rfl
  have hc6 : Nat.choose 24 6 = 134596 := rfl
  have hs7 : 24 - 7 = 17 := rfl
  have hc7 : Nat.choose 24 7 = 346104 := rfl
  have hs8 : 24 - 8 = 16 := rfl
  have hc8 : Nat.choose 24 8 = 735471 := rfl
  have hs9 : 24 - 9 = 15 := rfl
  have hc9 : Nat.choose 24 9 = 1307504 := rfl
  have hs10 : 24 - 10 = 14 := rfl
  have hc10 : Nat.choose 24 10 = 1961256 := rfl
  have hs11 : 24 - 11 = 13 := rfl
  have hc11 : Nat.choose 24 11 = 2496144 := rfl
  have hs12 : 24 - 12 = 12 := rfl
  have hc12 : Nat.choose 24 12 = 2704156 := rfl
  have hs13 : 24 - 13 = 11 := rfl
  have hc13 : Nat.choose 24 13 = 2496144 := rfl
  have hs14 : 24 - 14 = 10 := rfl
  have hc14 : Nat.choose 24 14 = 1961256 := rfl
  have hs15 : 24 - 15 = 9 := rfl
  have hc15 : Nat.choose 24 15 = 1307504 := rfl
  have hs16 : 24 - 16 = 8 := rfl
  have hc16 : Nat.choose 24 16 = 735471 := rfl
  have hs17 : 24 - 17 = 7 := rfl
  have hc17 : Nat.choose 24 17 = 346104 := rfl
  have hs18 : 24 - 18 = 6 := rfl
  have hc18 : Nat.choose 24 18 = 134596 := rfl
  have hs19 : 24 - 19 = 5 := rfl
  have hc19 : Nat.choose 24 19 = 42504 := rfl
  have hs20 : 24 - 20 = 4 := rfl
  have hc20 : Nat.choose 24 20 = 10626 := rfl
  have hs21 : 24 - 21 = 3 := rfl
  have hc21 : Nat.choose 24 21 = 2024 := rfl
  have hs22 : 24 - 22 = 2 := rfl
  have hc22 : Nat.choose 24 22 = 276 := rfl
  have hs23 : 24 - 23 = 1 := rfl
  have hc23 : Nat.choose 24 23 = 24 := rfl
  have hs24 : 24 - 24 = 0 := rfl
  have hc24 : Nat.choose 24 24 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_24 : A195441 (25 - 1) = 546 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 25 - 0 = 25 := rfl
  have hc0 : Nat.choose 25 0 = 1 := rfl
  have hs1 : 25 - 1 = 24 := rfl
  have hc1 : Nat.choose 25 1 = 25 := rfl
  have hs2 : 25 - 2 = 23 := rfl
  have hc2 : Nat.choose 25 2 = 300 := rfl
  have hs3 : 25 - 3 = 22 := rfl
  have hc3 : Nat.choose 25 3 = 2300 := rfl
  have hs4 : 25 - 4 = 21 := rfl
  have hc4 : Nat.choose 25 4 = 12650 := rfl
  have hs5 : 25 - 5 = 20 := rfl
  have hc5 : Nat.choose 25 5 = 53130 := rfl
  have hs6 : 25 - 6 = 19 := rfl
  have hc6 : Nat.choose 25 6 = 177100 := rfl
  have hs7 : 25 - 7 = 18 := rfl
  have hc7 : Nat.choose 25 7 = 480700 := rfl
  have hs8 : 25 - 8 = 17 := rfl
  have hc8 : Nat.choose 25 8 = 1081575 := rfl
  have hs9 : 25 - 9 = 16 := rfl
  have hc9 : Nat.choose 25 9 = 2042975 := rfl
  have hs10 : 25 - 10 = 15 := rfl
  have hc10 : Nat.choose 25 10 = 3268760 := rfl
  have hs11 : 25 - 11 = 14 := rfl
  have hc11 : Nat.choose 25 11 = 4457400 := rfl
  have hs12 : 25 - 12 = 13 := rfl
  have hc12 : Nat.choose 25 12 = 5200300 := rfl
  have hs13 : 25 - 13 = 12 := rfl
  have hc13 : Nat.choose 25 13 = 5200300 := rfl
  have hs14 : 25 - 14 = 11 := rfl
  have hc14 : Nat.choose 25 14 = 4457400 := rfl
  have hs15 : 25 - 15 = 10 := rfl
  have hc15 : Nat.choose 25 15 = 3268760 := rfl
  have hs16 : 25 - 16 = 9 := rfl
  have hc16 : Nat.choose 25 16 = 2042975 := rfl
  have hs17 : 25 - 17 = 8 := rfl
  have hc17 : Nat.choose 25 17 = 1081575 := rfl
  have hs18 : 25 - 18 = 7 := rfl
  have hc18 : Nat.choose 25 18 = 480700 := rfl
  have hs19 : 25 - 19 = 6 := rfl
  have hc19 : Nat.choose 25 19 = 177100 := rfl
  have hs20 : 25 - 20 = 5 := rfl
  have hc20 : Nat.choose 25 20 = 53130 := rfl
  have hs21 : 25 - 21 = 4 := rfl
  have hc21 : Nat.choose 25 21 = 12650 := rfl
  have hs22 : 25 - 22 = 3 := rfl
  have hc22 : Nat.choose 25 22 = 2300 := rfl
  have hs23 : 25 - 23 = 2 := rfl
  have hc23 : Nat.choose 25 23 = 300 := rfl
  have hs24 : 25 - 24 = 1 := rfl
  have hc24 : Nat.choose 25 24 = 25 := rfl
  have hs25 : 25 - 25 = 0 := rfl
  have hc25 : Nat.choose 25 25 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_25 : A195441 (26 - 1) = 42 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 26 - 0 = 26 := rfl
  have hc0 : Nat.choose 26 0 = 1 := rfl
  have hs1 : 26 - 1 = 25 := rfl
  have hc1 : Nat.choose 26 1 = 26 := rfl
  have hs2 : 26 - 2 = 24 := rfl
  have hc2 : Nat.choose 26 2 = 325 := rfl
  have hs3 : 26 - 3 = 23 := rfl
  have hc3 : Nat.choose 26 3 = 2600 := rfl
  have hs4 : 26 - 4 = 22 := rfl
  have hc4 : Nat.choose 26 4 = 14950 := rfl
  have hs5 : 26 - 5 = 21 := rfl
  have hc5 : Nat.choose 26 5 = 65780 := rfl
  have hs6 : 26 - 6 = 20 := rfl
  have hc6 : Nat.choose 26 6 = 230230 := rfl
  have hs7 : 26 - 7 = 19 := rfl
  have hc7 : Nat.choose 26 7 = 657800 := rfl
  have hs8 : 26 - 8 = 18 := rfl
  have hc8 : Nat.choose 26 8 = 1562275 := rfl
  have hs9 : 26 - 9 = 17 := rfl
  have hc9 : Nat.choose 26 9 = 3124550 := rfl
  have hs10 : 26 - 10 = 16 := rfl
  have hc10 : Nat.choose 26 10 = 5311735 := rfl
  have hs11 : 26 - 11 = 15 := rfl
  have hc11 : Nat.choose 26 11 = 7726160 := rfl
  have hs12 : 26 - 12 = 14 := rfl
  have hc12 : Nat.choose 26 12 = 9657700 := rfl
  have hs13 : 26 - 13 = 13 := rfl
  have hc13 : Nat.choose 26 13 = 10400600 := rfl
  have hs14 : 26 - 14 = 12 := rfl
  have hc14 : Nat.choose 26 14 = 9657700 := rfl
  have hs15 : 26 - 15 = 11 := rfl
  have hc15 : Nat.choose 26 15 = 7726160 := rfl
  have hs16 : 26 - 16 = 10 := rfl
  have hc16 : Nat.choose 26 16 = 5311735 := rfl
  have hs17 : 26 - 17 = 9 := rfl
  have hc17 : Nat.choose 26 17 = 3124550 := rfl
  have hs18 : 26 - 18 = 8 := rfl
  have hc18 : Nat.choose 26 18 = 1562275 := rfl
  have hs19 : 26 - 19 = 7 := rfl
  have hc19 : Nat.choose 26 19 = 657800 := rfl
  have hs20 : 26 - 20 = 6 := rfl
  have hc20 : Nat.choose 26 20 = 230230 := rfl
  have hs21 : 26 - 21 = 5 := rfl
  have hc21 : Nat.choose 26 21 = 65780 := rfl
  have hs22 : 26 - 22 = 4 := rfl
  have hc22 : Nat.choose 26 22 = 14950 := rfl
  have hs23 : 26 - 23 = 3 := rfl
  have hc23 : Nat.choose 26 23 = 2600 := rfl
  have hs24 : 26 - 24 = 2 := rfl
  have hc24 : Nat.choose 26 24 = 325 := rfl
  have hs25 : 26 - 25 = 1 := rfl
  have hc25 : Nat.choose 26 25 = 26 := rfl
  have hs26 : 26 - 26 = 0 := rfl
  have hc26 : Nat.choose 26 26 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_26 : A195441 (27 - 1) = 14 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 27 - 0 = 27 := rfl
  have hc0 : Nat.choose 27 0 = 1 := rfl
  have hs1 : 27 - 1 = 26 := rfl
  have hc1 : Nat.choose 27 1 = 27 := rfl
  have hs2 : 27 - 2 = 25 := rfl
  have hc2 : Nat.choose 27 2 = 351 := rfl
  have hs3 : 27 - 3 = 24 := rfl
  have hc3 : Nat.choose 27 3 = 2925 := rfl
  have hs4 : 27 - 4 = 23 := rfl
  have hc4 : Nat.choose 27 4 = 17550 := rfl
  have hs5 : 27 - 5 = 22 := rfl
  have hc5 : Nat.choose 27 5 = 80730 := rfl
  have hs6 : 27 - 6 = 21 := rfl
  have hc6 : Nat.choose 27 6 = 296010 := rfl
  have hs7 : 27 - 7 = 20 := rfl
  have hc7 : Nat.choose 27 7 = 888030 := rfl
  have hs8 : 27 - 8 = 19 := rfl
  have hc8 : Nat.choose 27 8 = 2220075 := rfl
  have hs9 : 27 - 9 = 18 := rfl
  have hc9 : Nat.choose 27 9 = 4686825 := rfl
  have hs10 : 27 - 10 = 17 := rfl
  have hc10 : Nat.choose 27 10 = 8436285 := rfl
  have hs11 : 27 - 11 = 16 := rfl
  have hc11 : Nat.choose 27 11 = 13037895 := rfl
  have hs12 : 27 - 12 = 15 := rfl
  have hc12 : Nat.choose 27 12 = 17383860 := rfl
  have hs13 : 27 - 13 = 14 := rfl
  have hc13 : Nat.choose 27 13 = 20058300 := rfl
  have hs14 : 27 - 14 = 13 := rfl
  have hc14 : Nat.choose 27 14 = 20058300 := rfl
  have hs15 : 27 - 15 = 12 := rfl
  have hc15 : Nat.choose 27 15 = 17383860 := rfl
  have hs16 : 27 - 16 = 11 := rfl
  have hc16 : Nat.choose 27 16 = 13037895 := rfl
  have hs17 : 27 - 17 = 10 := rfl
  have hc17 : Nat.choose 27 17 = 8436285 := rfl
  have hs18 : 27 - 18 = 9 := rfl
  have hc18 : Nat.choose 27 18 = 4686825 := rfl
  have hs19 : 27 - 19 = 8 := rfl
  have hc19 : Nat.choose 27 19 = 2220075 := rfl
  have hs20 : 27 - 20 = 7 := rfl
  have hc20 : Nat.choose 27 20 = 888030 := rfl
  have hs21 : 27 - 21 = 6 := rfl
  have hc21 : Nat.choose 27 21 = 296010 := rfl
  have hs22 : 27 - 22 = 5 := rfl
  have hc22 : Nat.choose 27 22 = 80730 := rfl
  have hs23 : 27 - 23 = 4 := rfl
  have hc23 : Nat.choose 27 23 = 17550 := rfl
  have hs24 : 27 - 24 = 3 := rfl
  have hc24 : Nat.choose 27 24 = 2925 := rfl
  have hs25 : 27 - 25 = 2 := rfl
  have hc25 : Nat.choose 27 25 = 351 := rfl
  have hs26 : 27 - 26 = 1 := rfl
  have hc26 : Nat.choose 27 26 = 27 := rfl
  have hs27 : 27 - 27 = 0 := rfl
  have hc27 : Nat.choose 27 27 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_27 : A195441 (28 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 28 - 0 = 28 := rfl
  have hc0 : Nat.choose 28 0 = 1 := rfl
  have hs1 : 28 - 1 = 27 := rfl
  have hc1 : Nat.choose 28 1 = 28 := rfl
  have hs2 : 28 - 2 = 26 := rfl
  have hc2 : Nat.choose 28 2 = 378 := rfl
  have hs3 : 28 - 3 = 25 := rfl
  have hc3 : Nat.choose 28 3 = 3276 := rfl
  have hs4 : 28 - 4 = 24 := rfl
  have hc4 : Nat.choose 28 4 = 20475 := rfl
  have hs5 : 28 - 5 = 23 := rfl
  have hc5 : Nat.choose 28 5 = 98280 := rfl
  have hs6 : 28 - 6 = 22 := rfl
  have hc6 : Nat.choose 28 6 = 376740 := rfl
  have hs7 : 28 - 7 = 21 := rfl
  have hc7 : Nat.choose 28 7 = 1184040 := rfl
  have hs8 : 28 - 8 = 20 := rfl
  have hc8 : Nat.choose 28 8 = 3108105 := rfl
  have hs9 : 28 - 9 = 19 := rfl
  have hc9 : Nat.choose 28 9 = 6906900 := rfl
  have hs10 : 28 - 10 = 18 := rfl
  have hc10 : Nat.choose 28 10 = 13123110 := rfl
  have hs11 : 28 - 11 = 17 := rfl
  have hc11 : Nat.choose 28 11 = 21474180 := rfl
  have hs12 : 28 - 12 = 16 := rfl
  have hc12 : Nat.choose 28 12 = 30421755 := rfl
  have hs13 : 28 - 13 = 15 := rfl
  have hc13 : Nat.choose 28 13 = 37442160 := rfl
  have hs14 : 28 - 14 = 14 := rfl
  have hc14 : Nat.choose 28 14 = 40116600 := rfl
  have hs15 : 28 - 15 = 13 := rfl
  have hc15 : Nat.choose 28 15 = 37442160 := rfl
  have hs16 : 28 - 16 = 12 := rfl
  have hc16 : Nat.choose 28 16 = 30421755 := rfl
  have hs17 : 28 - 17 = 11 := rfl
  have hc17 : Nat.choose 28 17 = 21474180 := rfl
  have hs18 : 28 - 18 = 10 := rfl
  have hc18 : Nat.choose 28 18 = 13123110 := rfl
  have hs19 : 28 - 19 = 9 := rfl
  have hc19 : Nat.choose 28 19 = 6906900 := rfl
  have hs20 : 28 - 20 = 8 := rfl
  have hc20 : Nat.choose 28 20 = 3108105 := rfl
  have hs21 : 28 - 21 = 7 := rfl
  have hc21 : Nat.choose 28 21 = 1184040 := rfl
  have hs22 : 28 - 22 = 6 := rfl
  have hc22 : Nat.choose 28 22 = 376740 := rfl
  have hs23 : 28 - 23 = 5 := rfl
  have hc23 : Nat.choose 28 23 = 98280 := rfl
  have hs24 : 28 - 24 = 4 := rfl
  have hc24 : Nat.choose 28 24 = 20475 := rfl
  have hs25 : 28 - 25 = 3 := rfl
  have hc25 : Nat.choose 28 25 = 3276 := rfl
  have hs26 : 28 - 26 = 2 := rfl
  have hc26 : Nat.choose 28 26 = 378 := rfl
  have hs27 : 28 - 27 = 1 := rfl
  have hc27 : Nat.choose 28 27 = 28 := rfl
  have hs28 : 28 - 28 = 0 := rfl
  have hc28 : Nat.choose 28 28 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_28 : A195441 (29 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 29 - 0 = 29 := rfl
  have hc0 : Nat.choose 29 0 = 1 := rfl
  have hs1 : 29 - 1 = 28 := rfl
  have hc1 : Nat.choose 29 1 = 29 := rfl
  have hs2 : 29 - 2 = 27 := rfl
  have hc2 : Nat.choose 29 2 = 406 := rfl
  have hs3 : 29 - 3 = 26 := rfl
  have hc3 : Nat.choose 29 3 = 3654 := rfl
  have hs4 : 29 - 4 = 25 := rfl
  have hc4 : Nat.choose 29 4 = 23751 := rfl
  have hs5 : 29 - 5 = 24 := rfl
  have hc5 : Nat.choose 29 5 = 118755 := rfl
  have hs6 : 29 - 6 = 23 := rfl
  have hc6 : Nat.choose 29 6 = 475020 := rfl
  have hs7 : 29 - 7 = 22 := rfl
  have hc7 : Nat.choose 29 7 = 1560780 := rfl
  have hs8 : 29 - 8 = 21 := rfl
  have hc8 : Nat.choose 29 8 = 4292145 := rfl
  have hs9 : 29 - 9 = 20 := rfl
  have hc9 : Nat.choose 29 9 = 10015005 := rfl
  have hs10 : 29 - 10 = 19 := rfl
  have hc10 : Nat.choose 29 10 = 20030010 := rfl
  have hs11 : 29 - 11 = 18 := rfl
  have hc11 : Nat.choose 29 11 = 34597290 := rfl
  have hs12 : 29 - 12 = 17 := rfl
  have hc12 : Nat.choose 29 12 = 51895935 := rfl
  have hs13 : 29 - 13 = 16 := rfl
  have hc13 : Nat.choose 29 13 = 67863915 := rfl
  have hs14 : 29 - 14 = 15 := rfl
  have hc14 : Nat.choose 29 14 = 77558760 := rfl
  have hs15 : 29 - 15 = 14 := rfl
  have hc15 : Nat.choose 29 15 = 77558760 := rfl
  have hs16 : 29 - 16 = 13 := rfl
  have hc16 : Nat.choose 29 16 = 67863915 := rfl
  have hs17 : 29 - 17 = 12 := rfl
  have hc17 : Nat.choose 29 17 = 51895935 := rfl
  have hs18 : 29 - 18 = 11 := rfl
  have hc18 : Nat.choose 29 18 = 34597290 := rfl
  have hs19 : 29 - 19 = 10 := rfl
  have hc19 : Nat.choose 29 19 = 20030010 := rfl
  have hs20 : 29 - 20 = 9 := rfl
  have hc20 : Nat.choose 29 20 = 10015005 := rfl
  have hs21 : 29 - 21 = 8 := rfl
  have hc21 : Nat.choose 29 21 = 4292145 := rfl
  have hs22 : 29 - 22 = 7 := rfl
  have hc22 : Nat.choose 29 22 = 1560780 := rfl
  have hs23 : 29 - 23 = 6 := rfl
  have hc23 : Nat.choose 29 23 = 475020 := rfl
  have hs24 : 29 - 24 = 5 := rfl
  have hc24 : Nat.choose 29 24 = 118755 := rfl
  have hs25 : 29 - 25 = 4 := rfl
  have hc25 : Nat.choose 29 25 = 23751 := rfl
  have hs26 : 29 - 26 = 3 := rfl
  have hc26 : Nat.choose 29 26 = 3654 := rfl
  have hs27 : 29 - 27 = 2 := rfl
  have hc27 : Nat.choose 29 27 = 406 := rfl
  have hs28 : 29 - 28 = 1 := rfl
  have hc28 : Nat.choose 29 28 = 29 := rfl
  have hs29 : 29 - 29 = 0 := rfl
  have hc29 : Nat.choose 29 29 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_29 : A195441 (30 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 30 - 0 = 30 := rfl
  have hc0 : Nat.choose 30 0 = 1 := rfl
  have hs1 : 30 - 1 = 29 := rfl
  have hc1 : Nat.choose 30 1 = 30 := rfl
  have hs2 : 30 - 2 = 28 := rfl
  have hc2 : Nat.choose 30 2 = 435 := rfl
  have hs3 : 30 - 3 = 27 := rfl
  have hc3 : Nat.choose 30 3 = 4060 := rfl
  have hs4 : 30 - 4 = 26 := rfl
  have hc4 : Nat.choose 30 4 = 27405 := rfl
  have hs5 : 30 - 5 = 25 := rfl
  have hc5 : Nat.choose 30 5 = 142506 := rfl
  have hs6 : 30 - 6 = 24 := rfl
  have hc6 : Nat.choose 30 6 = 593775 := rfl
  have hs7 : 30 - 7 = 23 := rfl
  have hc7 : Nat.choose 30 7 = 2035800 := rfl
  have hs8 : 30 - 8 = 22 := rfl
  have hc8 : Nat.choose 30 8 = 5852925 := rfl
  have hs9 : 30 - 9 = 21 := rfl
  have hc9 : Nat.choose 30 9 = 14307150 := rfl
  have hs10 : 30 - 10 = 20 := rfl
  have hc10 : Nat.choose 30 10 = 30045015 := rfl
  have hs11 : 30 - 11 = 19 := rfl
  have hc11 : Nat.choose 30 11 = 54627300 := rfl
  have hs12 : 30 - 12 = 18 := rfl
  have hc12 : Nat.choose 30 12 = 86493225 := rfl
  have hs13 : 30 - 13 = 17 := rfl
  have hc13 : Nat.choose 30 13 = 119759850 := rfl
  have hs14 : 30 - 14 = 16 := rfl
  have hc14 : Nat.choose 30 14 = 145422675 := rfl
  have hs15 : 30 - 15 = 15 := rfl
  have hc15 : Nat.choose 30 15 = 155117520 := rfl
  have hs16 : 30 - 16 = 14 := rfl
  have hc16 : Nat.choose 30 16 = 145422675 := rfl
  have hs17 : 30 - 17 = 13 := rfl
  have hc17 : Nat.choose 30 17 = 119759850 := rfl
  have hs18 : 30 - 18 = 12 := rfl
  have hc18 : Nat.choose 30 18 = 86493225 := rfl
  have hs19 : 30 - 19 = 11 := rfl
  have hc19 : Nat.choose 30 19 = 54627300 := rfl
  have hs20 : 30 - 20 = 10 := rfl
  have hc20 : Nat.choose 30 20 = 30045015 := rfl
  have hs21 : 30 - 21 = 9 := rfl
  have hc21 : Nat.choose 30 21 = 14307150 := rfl
  have hs22 : 30 - 22 = 8 := rfl
  have hc22 : Nat.choose 30 22 = 5852925 := rfl
  have hs23 : 30 - 23 = 7 := rfl
  have hc23 : Nat.choose 30 23 = 2035800 := rfl
  have hs24 : 30 - 24 = 6 := rfl
  have hc24 : Nat.choose 30 24 = 593775 := rfl
  have hs25 : 30 - 25 = 5 := rfl
  have hc25 : Nat.choose 30 25 = 142506 := rfl
  have hs26 : 30 - 26 = 4 := rfl
  have hc26 : Nat.choose 30 26 = 27405 := rfl
  have hs27 : 30 - 27 = 3 := rfl
  have hc27 : Nat.choose 30 27 = 4060 := rfl
  have hs28 : 30 - 28 = 2 := rfl
  have hc28 : Nat.choose 30 28 = 435 := rfl
  have hs29 : 30 - 29 = 1 := rfl
  have hc29 : Nat.choose 30 29 = 30 := rfl
  have hs30 : 30 - 30 = 0 := rfl
  have hc30 : Nat.choose 30 30 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_30 : A195441 (31 - 1) = 462 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 31 - 0 = 31 := rfl
  have hc0 : Nat.choose 31 0 = 1 := rfl
  have hs1 : 31 - 1 = 30 := rfl
  have hc1 : Nat.choose 31 1 = 31 := rfl
  have hs2 : 31 - 2 = 29 := rfl
  have hc2 : Nat.choose 31 2 = 465 := rfl
  have hs3 : 31 - 3 = 28 := rfl
  have hc3 : Nat.choose 31 3 = 4495 := rfl
  have hs4 : 31 - 4 = 27 := rfl
  have hc4 : Nat.choose 31 4 = 31465 := rfl
  have hs5 : 31 - 5 = 26 := rfl
  have hc5 : Nat.choose 31 5 = 169911 := rfl
  have hs6 : 31 - 6 = 25 := rfl
  have hc6 : Nat.choose 31 6 = 736281 := rfl
  have hs7 : 31 - 7 = 24 := rfl
  have hc7 : Nat.choose 31 7 = 2629575 := rfl
  have hs8 : 31 - 8 = 23 := rfl
  have hc8 : Nat.choose 31 8 = 7888725 := rfl
  have hs9 : 31 - 9 = 22 := rfl
  have hc9 : Nat.choose 31 9 = 20160075 := rfl
  have hs10 : 31 - 10 = 21 := rfl
  have hc10 : Nat.choose 31 10 = 44352165 := rfl
  have hs11 : 31 - 11 = 20 := rfl
  have hc11 : Nat.choose 31 11 = 84672315 := rfl
  have hs12 : 31 - 12 = 19 := rfl
  have hc12 : Nat.choose 31 12 = 141120525 := rfl
  have hs13 : 31 - 13 = 18 := rfl
  have hc13 : Nat.choose 31 13 = 206253075 := rfl
  have hs14 : 31 - 14 = 17 := rfl
  have hc14 : Nat.choose 31 14 = 265182525 := rfl
  have hs15 : 31 - 15 = 16 := rfl
  have hc15 : Nat.choose 31 15 = 300540195 := rfl
  have hs16 : 31 - 16 = 15 := rfl
  have hc16 : Nat.choose 31 16 = 300540195 := rfl
  have hs17 : 31 - 17 = 14 := rfl
  have hc17 : Nat.choose 31 17 = 265182525 := rfl
  have hs18 : 31 - 18 = 13 := rfl
  have hc18 : Nat.choose 31 18 = 206253075 := rfl
  have hs19 : 31 - 19 = 12 := rfl
  have hc19 : Nat.choose 31 19 = 141120525 := rfl
  have hs20 : 31 - 20 = 11 := rfl
  have hc20 : Nat.choose 31 20 = 84672315 := rfl
  have hs21 : 31 - 21 = 10 := rfl
  have hc21 : Nat.choose 31 21 = 44352165 := rfl
  have hs22 : 31 - 22 = 9 := rfl
  have hc22 : Nat.choose 31 22 = 20160075 := rfl
  have hs23 : 31 - 23 = 8 := rfl
  have hc23 : Nat.choose 31 23 = 7888725 := rfl
  have hs24 : 31 - 24 = 7 := rfl
  have hc24 : Nat.choose 31 24 = 2629575 := rfl
  have hs25 : 31 - 25 = 6 := rfl
  have hc25 : Nat.choose 31 25 = 736281 := rfl
  have hs26 : 31 - 26 = 5 := rfl
  have hc26 : Nat.choose 31 26 = 169911 := rfl
  have hs27 : 31 - 27 = 4 := rfl
  have hc27 : Nat.choose 31 27 = 31465 := rfl
  have hs28 : 31 - 28 = 3 := rfl
  have hc28 : Nat.choose 31 28 = 4495 := rfl
  have hs29 : 31 - 29 = 2 := rfl
  have hc29 : Nat.choose 31 29 = 465 := rfl
  have hs30 : 31 - 30 = 1 := rfl
  have hc30 : Nat.choose 31 30 = 31 := rfl
  have hs31 : 31 - 31 = 0 := rfl
  have hc31 : Nat.choose 31 31 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_31 : A195441 (32 - 1) = 231 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 32 - 0 = 32 := rfl
  have hc0 : Nat.choose 32 0 = 1 := rfl
  have hs1 : 32 - 1 = 31 := rfl
  have hc1 : Nat.choose 32 1 = 32 := rfl
  have hs2 : 32 - 2 = 30 := rfl
  have hc2 : Nat.choose 32 2 = 496 := rfl
  have hs3 : 32 - 3 = 29 := rfl
  have hc3 : Nat.choose 32 3 = 4960 := rfl
  have hs4 : 32 - 4 = 28 := rfl
  have hc4 : Nat.choose 32 4 = 35960 := rfl
  have hs5 : 32 - 5 = 27 := rfl
  have hc5 : Nat.choose 32 5 = 201376 := rfl
  have hs6 : 32 - 6 = 26 := rfl
  have hc6 : Nat.choose 32 6 = 906192 := rfl
  have hs7 : 32 - 7 = 25 := rfl
  have hc7 : Nat.choose 32 7 = 3365856 := rfl
  have hs8 : 32 - 8 = 24 := rfl
  have hc8 : Nat.choose 32 8 = 10518300 := rfl
  have hs9 : 32 - 9 = 23 := rfl
  have hc9 : Nat.choose 32 9 = 28048800 := rfl
  have hs10 : 32 - 10 = 22 := rfl
  have hc10 : Nat.choose 32 10 = 64512240 := rfl
  have hs11 : 32 - 11 = 21 := rfl
  have hc11 : Nat.choose 32 11 = 129024480 := rfl
  have hs12 : 32 - 12 = 20 := rfl
  have hc12 : Nat.choose 32 12 = 225792840 := rfl
  have hs13 : 32 - 13 = 19 := rfl
  have hc13 : Nat.choose 32 13 = 347373600 := rfl
  have hs14 : 32 - 14 = 18 := rfl
  have hc14 : Nat.choose 32 14 = 471435600 := rfl
  have hs15 : 32 - 15 = 17 := rfl
  have hc15 : Nat.choose 32 15 = 565722720 := rfl
  have hs16 : 32 - 16 = 16 := rfl
  have hc16 : Nat.choose 32 16 = 601080390 := rfl
  have hs17 : 32 - 17 = 15 := rfl
  have hc17 : Nat.choose 32 17 = 565722720 := rfl
  have hs18 : 32 - 18 = 14 := rfl
  have hc18 : Nat.choose 32 18 = 471435600 := rfl
  have hs19 : 32 - 19 = 13 := rfl
  have hc19 : Nat.choose 32 19 = 347373600 := rfl
  have hs20 : 32 - 20 = 12 := rfl
  have hc20 : Nat.choose 32 20 = 225792840 := rfl
  have hs21 : 32 - 21 = 11 := rfl
  have hc21 : Nat.choose 32 21 = 129024480 := rfl
  have hs22 : 32 - 22 = 10 := rfl
  have hc22 : Nat.choose 32 22 = 64512240 := rfl
  have hs23 : 32 - 23 = 9 := rfl
  have hc23 : Nat.choose 32 23 = 28048800 := rfl
  have hs24 : 32 - 24 = 8 := rfl
  have hc24 : Nat.choose 32 24 = 10518300 := rfl
  have hs25 : 32 - 25 = 7 := rfl
  have hc25 : Nat.choose 32 25 = 3365856 := rfl
  have hs26 : 32 - 26 = 6 := rfl
  have hc26 : Nat.choose 32 26 = 906192 := rfl
  have hs27 : 32 - 27 = 5 := rfl
  have hc27 : Nat.choose 32 27 = 201376 := rfl
  have hs28 : 32 - 28 = 4 := rfl
  have hc28 : Nat.choose 32 28 = 35960 := rfl
  have hs29 : 32 - 29 = 3 := rfl
  have hc29 : Nat.choose 32 29 = 4960 := rfl
  have hs30 : 32 - 30 = 2 := rfl
  have hc30 : Nat.choose 32 30 = 496 := rfl
  have hs31 : 32 - 31 = 1 := rfl
  have hc31 : Nat.choose 32 31 = 32 := rfl
  have hs32 : 32 - 32 = 0 := rfl
  have hc32 : Nat.choose 32 32 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_32 : A195441 (33 - 1) = 3570 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 33 - 0 = 33 := rfl
  have hc0 : Nat.choose 33 0 = 1 := rfl
  have hs1 : 33 - 1 = 32 := rfl
  have hc1 : Nat.choose 33 1 = 33 := rfl
  have hs2 : 33 - 2 = 31 := rfl
  have hc2 : Nat.choose 33 2 = 528 := rfl
  have hs3 : 33 - 3 = 30 := rfl
  have hc3 : Nat.choose 33 3 = 5456 := rfl
  have hs4 : 33 - 4 = 29 := rfl
  have hc4 : Nat.choose 33 4 = 40920 := rfl
  have hs5 : 33 - 5 = 28 := rfl
  have hc5 : Nat.choose 33 5 = 237336 := rfl
  have hs6 : 33 - 6 = 27 := rfl
  have hc6 : Nat.choose 33 6 = 1107568 := rfl
  have hs7 : 33 - 7 = 26 := rfl
  have hc7 : Nat.choose 33 7 = 4272048 := rfl
  have hs8 : 33 - 8 = 25 := rfl
  have hc8 : Nat.choose 33 8 = 13884156 := rfl
  have hs9 : 33 - 9 = 24 := rfl
  have hc9 : Nat.choose 33 9 = 38567100 := rfl
  have hs10 : 33 - 10 = 23 := rfl
  have hc10 : Nat.choose 33 10 = 92561040 := rfl
  have hs11 : 33 - 11 = 22 := rfl
  have hc11 : Nat.choose 33 11 = 193536720 := rfl
  have hs12 : 33 - 12 = 21 := rfl
  have hc12 : Nat.choose 33 12 = 354817320 := rfl
  have hs13 : 33 - 13 = 20 := rfl
  have hc13 : Nat.choose 33 13 = 573166440 := rfl
  have hs14 : 33 - 14 = 19 := rfl
  have hc14 : Nat.choose 33 14 = 818809200 := rfl
  have hs15 : 33 - 15 = 18 := rfl
  have hc15 : Nat.choose 33 15 = 1037158320 := rfl
  have hs16 : 33 - 16 = 17 := rfl
  have hc16 : Nat.choose 33 16 = 1166803110 := rfl
  have hs17 : 33 - 17 = 16 := rfl
  have hc17 : Nat.choose 33 17 = 1166803110 := rfl
  have hs18 : 33 - 18 = 15 := rfl
  have hc18 : Nat.choose 33 18 = 1037158320 := rfl
  have hs19 : 33 - 19 = 14 := rfl
  have hc19 : Nat.choose 33 19 = 818809200 := rfl
  have hs20 : 33 - 20 = 13 := rfl
  have hc20 : Nat.choose 33 20 = 573166440 := rfl
  have hs21 : 33 - 21 = 12 := rfl
  have hc21 : Nat.choose 33 21 = 354817320 := rfl
  have hs22 : 33 - 22 = 11 := rfl
  have hc22 : Nat.choose 33 22 = 193536720 := rfl
  have hs23 : 33 - 23 = 10 := rfl
  have hc23 : Nat.choose 33 23 = 92561040 := rfl
  have hs24 : 33 - 24 = 9 := rfl
  have hc24 : Nat.choose 33 24 = 38567100 := rfl
  have hs25 : 33 - 25 = 8 := rfl
  have hc25 : Nat.choose 33 25 = 13884156 := rfl
  have hs26 : 33 - 26 = 7 := rfl
  have hc26 : Nat.choose 33 26 = 4272048 := rfl
  have hs27 : 33 - 27 = 6 := rfl
  have hc27 : Nat.choose 33 27 = 1107568 := rfl
  have hs28 : 33 - 28 = 5 := rfl
  have hc28 : Nat.choose 33 28 = 237336 := rfl
  have hs29 : 33 - 29 = 4 := rfl
  have hc29 : Nat.choose 33 29 = 40920 := rfl
  have hs30 : 33 - 30 = 3 := rfl
  have hc30 : Nat.choose 33 30 = 5456 := rfl
  have hs31 : 33 - 31 = 2 := rfl
  have hc31 : Nat.choose 33 31 = 528 := rfl
  have hs32 : 33 - 32 = 1 := rfl
  have hc32 : Nat.choose 33 32 = 33 := rfl
  have hs33 : 33 - 33 = 0 := rfl
  have hc33 : Nat.choose 33 33 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_33 : A195441 (34 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 34 - 0 = 34 := rfl
  have hc0 : Nat.choose 34 0 = 1 := rfl
  have hs1 : 34 - 1 = 33 := rfl
  have hc1 : Nat.choose 34 1 = 34 := rfl
  have hs2 : 34 - 2 = 32 := rfl
  have hc2 : Nat.choose 34 2 = 561 := rfl
  have hs3 : 34 - 3 = 31 := rfl
  have hc3 : Nat.choose 34 3 = 5984 := rfl
  have hs4 : 34 - 4 = 30 := rfl
  have hc4 : Nat.choose 34 4 = 46376 := rfl
  have hs5 : 34 - 5 = 29 := rfl
  have hc5 : Nat.choose 34 5 = 278256 := rfl
  have hs6 : 34 - 6 = 28 := rfl
  have hc6 : Nat.choose 34 6 = 1344904 := rfl
  have hs7 : 34 - 7 = 27 := rfl
  have hc7 : Nat.choose 34 7 = 5379616 := rfl
  have hs8 : 34 - 8 = 26 := rfl
  have hc8 : Nat.choose 34 8 = 18156204 := rfl
  have hs9 : 34 - 9 = 25 := rfl
  have hc9 : Nat.choose 34 9 = 52451256 := rfl
  have hs10 : 34 - 10 = 24 := rfl
  have hc10 : Nat.choose 34 10 = 131128140 := rfl
  have hs11 : 34 - 11 = 23 := rfl
  have hc11 : Nat.choose 34 11 = 286097760 := rfl
  have hs12 : 34 - 12 = 22 := rfl
  have hc12 : Nat.choose 34 12 = 548354040 := rfl
  have hs13 : 34 - 13 = 21 := rfl
  have hc13 : Nat.choose 34 13 = 927983760 := rfl
  have hs14 : 34 - 14 = 20 := rfl
  have hc14 : Nat.choose 34 14 = 1391975640 := rfl
  have hs15 : 34 - 15 = 19 := rfl
  have hc15 : Nat.choose 34 15 = 1855967520 := rfl
  have hs16 : 34 - 16 = 18 := rfl
  have hc16 : Nat.choose 34 16 = 2203961430 := rfl
  have hs17 : 34 - 17 = 17 := rfl
  have hc17 : Nat.choose 34 17 = 2333606220 := rfl
  have hs18 : 34 - 18 = 16 := rfl
  have hc18 : Nat.choose 34 18 = 2203961430 := rfl
  have hs19 : 34 - 19 = 15 := rfl
  have hc19 : Nat.choose 34 19 = 1855967520 := rfl
  have hs20 : 34 - 20 = 14 := rfl
  have hc20 : Nat.choose 34 20 = 1391975640 := rfl
  have hs21 : 34 - 21 = 13 := rfl
  have hc21 : Nat.choose 34 21 = 927983760 := rfl
  have hs22 : 34 - 22 = 12 := rfl
  have hc22 : Nat.choose 34 22 = 548354040 := rfl
  have hs23 : 34 - 23 = 11 := rfl
  have hc23 : Nat.choose 34 23 = 286097760 := rfl
  have hs24 : 34 - 24 = 10 := rfl
  have hc24 : Nat.choose 34 24 = 131128140 := rfl
  have hs25 : 34 - 25 = 9 := rfl
  have hc25 : Nat.choose 34 25 = 52451256 := rfl
  have hs26 : 34 - 26 = 8 := rfl
  have hc26 : Nat.choose 34 26 = 18156204 := rfl
  have hs27 : 34 - 27 = 7 := rfl
  have hc27 : Nat.choose 34 27 = 5379616 := rfl
  have hs28 : 34 - 28 = 6 := rfl
  have hc28 : Nat.choose 34 28 = 1344904 := rfl
  have hs29 : 34 - 29 = 5 := rfl
  have hc29 : Nat.choose 34 29 = 278256 := rfl
  have hs30 : 34 - 30 = 4 := rfl
  have hc30 : Nat.choose 34 30 = 46376 := rfl
  have hs31 : 34 - 31 = 3 := rfl
  have hc31 : Nat.choose 34 31 = 5984 := rfl
  have hs32 : 34 - 32 = 2 := rfl
  have hc32 : Nat.choose 34 32 = 561 := rfl
  have hs33 : 34 - 33 = 1 := rfl
  have hc33 : Nat.choose 34 33 = 34 := rfl
  have hs34 : 34 - 34 = 0 := rfl
  have hc34 : Nat.choose 34 34 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_34 : A195441 (35 - 1) = 6 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 35 - 0 = 35 := rfl
  have hc0 : Nat.choose 35 0 = 1 := rfl
  have hs1 : 35 - 1 = 34 := rfl
  have hc1 : Nat.choose 35 1 = 35 := rfl
  have hs2 : 35 - 2 = 33 := rfl
  have hc2 : Nat.choose 35 2 = 595 := rfl
  have hs3 : 35 - 3 = 32 := rfl
  have hc3 : Nat.choose 35 3 = 6545 := rfl
  have hs4 : 35 - 4 = 31 := rfl
  have hc4 : Nat.choose 35 4 = 52360 := rfl
  have hs5 : 35 - 5 = 30 := rfl
  have hc5 : Nat.choose 35 5 = 324632 := rfl
  have hs6 : 35 - 6 = 29 := rfl
  have hc6 : Nat.choose 35 6 = 1623160 := rfl
  have hs7 : 35 - 7 = 28 := rfl
  have hc7 : Nat.choose 35 7 = 6724520 := rfl
  have hs8 : 35 - 8 = 27 := rfl
  have hc8 : Nat.choose 35 8 = 23535820 := rfl
  have hs9 : 35 - 9 = 26 := rfl
  have hc9 : Nat.choose 35 9 = 70607460 := rfl
  have hs10 : 35 - 10 = 25 := rfl
  have hc10 : Nat.choose 35 10 = 183579396 := rfl
  have hs11 : 35 - 11 = 24 := rfl
  have hc11 : Nat.choose 35 11 = 417225900 := rfl
  have hs12 : 35 - 12 = 23 := rfl
  have hc12 : Nat.choose 35 12 = 834451800 := rfl
  have hs13 : 35 - 13 = 22 := rfl
  have hc13 : Nat.choose 35 13 = 1476337800 := rfl
  have hs14 : 35 - 14 = 21 := rfl
  have hc14 : Nat.choose 35 14 = 2319959400 := rfl
  have hs15 : 35 - 15 = 20 := rfl
  have hc15 : Nat.choose 35 15 = 3247943160 := rfl
  have hs16 : 35 - 16 = 19 := rfl
  have hc16 : Nat.choose 35 16 = 4059928950 := rfl
  have hs17 : 35 - 17 = 18 := rfl
  have hc17 : Nat.choose 35 17 = 4537567650 := rfl
  have hs18 : 35 - 18 = 17 := rfl
  have hc18 : Nat.choose 35 18 = 4537567650 := rfl
  have hs19 : 35 - 19 = 16 := rfl
  have hc19 : Nat.choose 35 19 = 4059928950 := rfl
  have hs20 : 35 - 20 = 15 := rfl
  have hc20 : Nat.choose 35 20 = 3247943160 := rfl
  have hs21 : 35 - 21 = 14 := rfl
  have hc21 : Nat.choose 35 21 = 2319959400 := rfl
  have hs22 : 35 - 22 = 13 := rfl
  have hc22 : Nat.choose 35 22 = 1476337800 := rfl
  have hs23 : 35 - 23 = 12 := rfl
  have hc23 : Nat.choose 35 23 = 834451800 := rfl
  have hs24 : 35 - 24 = 11 := rfl
  have hc24 : Nat.choose 35 24 = 417225900 := rfl
  have hs25 : 35 - 25 = 10 := rfl
  have hc25 : Nat.choose 35 25 = 183579396 := rfl
  have hs26 : 35 - 26 = 9 := rfl
  have hc26 : Nat.choose 35 26 = 70607460 := rfl
  have hs27 : 35 - 27 = 8 := rfl
  have hc27 : Nat.choose 35 27 = 23535820 := rfl
  have hs28 : 35 - 28 = 7 := rfl
  have hc28 : Nat.choose 35 28 = 6724520 := rfl
  have hs29 : 35 - 29 = 6 := rfl
  have hc29 : Nat.choose 35 29 = 1623160 := rfl
  have hs30 : 35 - 30 = 5 := rfl
  have hc30 : Nat.choose 35 30 = 324632 := rfl
  have hs31 : 35 - 31 = 4 := rfl
  have hc31 : Nat.choose 35 31 = 52360 := rfl
  have hs32 : 35 - 32 = 3 := rfl
  have hc32 : Nat.choose 35 32 = 6545 := rfl
  have hs33 : 35 - 33 = 2 := rfl
  have hc33 : Nat.choose 35 33 = 595 := rfl
  have hs34 : 35 - 34 = 1 := rfl
  have hc34 : Nat.choose 35 34 = 35 := rfl
  have hs35 : 35 - 35 = 0 := rfl
  have hc35 : Nat.choose 35 35 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_35 : A195441 (36 - 1) = 2 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 36 - 0 = 36 := rfl
  have hc0 : Nat.choose 36 0 = 1 := rfl
  have hs1 : 36 - 1 = 35 := rfl
  have hc1 : Nat.choose 36 1 = 36 := rfl
  have hs2 : 36 - 2 = 34 := rfl
  have hc2 : Nat.choose 36 2 = 630 := rfl
  have hs3 : 36 - 3 = 33 := rfl
  have hc3 : Nat.choose 36 3 = 7140 := rfl
  have hs4 : 36 - 4 = 32 := rfl
  have hc4 : Nat.choose 36 4 = 58905 := rfl
  have hs5 : 36 - 5 = 31 := rfl
  have hc5 : Nat.choose 36 5 = 376992 := rfl
  have hs6 : 36 - 6 = 30 := rfl
  have hc6 : Nat.choose 36 6 = 1947792 := rfl
  have hs7 : 36 - 7 = 29 := rfl
  have hc7 : Nat.choose 36 7 = 8347680 := rfl
  have hs8 : 36 - 8 = 28 := rfl
  have hc8 : Nat.choose 36 8 = 30260340 := rfl
  have hs9 : 36 - 9 = 27 := rfl
  have hc9 : Nat.choose 36 9 = 94143280 := rfl
  have hs10 : 36 - 10 = 26 := rfl
  have hc10 : Nat.choose 36 10 = 254186856 := rfl
  have hs11 : 36 - 11 = 25 := rfl
  have hc11 : Nat.choose 36 11 = 600805296 := rfl
  have hs12 : 36 - 12 = 24 := rfl
  have hc12 : Nat.choose 36 12 = 1251677700 := rfl
  have hs13 : 36 - 13 = 23 := rfl
  have hc13 : Nat.choose 36 13 = 2310789600 := rfl
  have hs14 : 36 - 14 = 22 := rfl
  have hc14 : Nat.choose 36 14 = 3796297200 := rfl
  have hs15 : 36 - 15 = 21 := rfl
  have hc15 : Nat.choose 36 15 = 5567902560 := rfl
  have hs16 : 36 - 16 = 20 := rfl
  have hc16 : Nat.choose 36 16 = 7307872110 := rfl
  have hs17 : 36 - 17 = 19 := rfl
  have hc17 : Nat.choose 36 17 = 8597496600 := rfl
  have hs18 : 36 - 18 = 18 := rfl
  have hc18 : Nat.choose 36 18 = 9075135300 := rfl
  have hs19 : 36 - 19 = 17 := rfl
  have hc19 : Nat.choose 36 19 = 8597496600 := rfl
  have hs20 : 36 - 20 = 16 := rfl
  have hc20 : Nat.choose 36 20 = 7307872110 := rfl
  have hs21 : 36 - 21 = 15 := rfl
  have hc21 : Nat.choose 36 21 = 5567902560 := rfl
  have hs22 : 36 - 22 = 14 := rfl
  have hc22 : Nat.choose 36 22 = 3796297200 := rfl
  have hs23 : 36 - 23 = 13 := rfl
  have hc23 : Nat.choose 36 23 = 2310789600 := rfl
  have hs24 : 36 - 24 = 12 := rfl
  have hc24 : Nat.choose 36 24 = 1251677700 := rfl
  have hs25 : 36 - 25 = 11 := rfl
  have hc25 : Nat.choose 36 25 = 600805296 := rfl
  have hs26 : 36 - 26 = 10 := rfl
  have hc26 : Nat.choose 36 26 = 254186856 := rfl
  have hs27 : 36 - 27 = 9 := rfl
  have hc27 : Nat.choose 36 27 = 94143280 := rfl
  have hs28 : 36 - 28 = 8 := rfl
  have hc28 : Nat.choose 36 28 = 30260340 := rfl
  have hs29 : 36 - 29 = 7 := rfl
  have hc29 : Nat.choose 36 29 = 8347680 := rfl
  have hs30 : 36 - 30 = 6 := rfl
  have hc30 : Nat.choose 36 30 = 1947792 := rfl
  have hs31 : 36 - 31 = 5 := rfl
  have hc31 : Nat.choose 36 31 = 376992 := rfl
  have hs32 : 36 - 32 = 4 := rfl
  have hc32 : Nat.choose 36 32 = 58905 := rfl
  have hs33 : 36 - 33 = 3 := rfl
  have hc33 : Nat.choose 36 33 = 7140 := rfl
  have hs34 : 36 - 34 = 2 := rfl
  have hc34 : Nat.choose 36 34 = 630 := rfl
  have hs35 : 36 - 35 = 1 := rfl
  have hc35 : Nat.choose 36 35 = 36 := rfl
  have hs36 : 36 - 36 = 0 := rfl
  have hc36 : Nat.choose 36 36 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_36 : A195441 (37 - 1) = 51870 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 37 - 0 = 37 := rfl
  have hc0 : Nat.choose 37 0 = 1 := rfl
  have hs1 : 37 - 1 = 36 := rfl
  have hc1 : Nat.choose 37 1 = 37 := rfl
  have hs2 : 37 - 2 = 35 := rfl
  have hc2 : Nat.choose 37 2 = 666 := rfl
  have hs3 : 37 - 3 = 34 := rfl
  have hc3 : Nat.choose 37 3 = 7770 := rfl
  have hs4 : 37 - 4 = 33 := rfl
  have hc4 : Nat.choose 37 4 = 66045 := rfl
  have hs5 : 37 - 5 = 32 := rfl
  have hc5 : Nat.choose 37 5 = 435897 := rfl
  have hs6 : 37 - 6 = 31 := rfl
  have hc6 : Nat.choose 37 6 = 2324784 := rfl
  have hs7 : 37 - 7 = 30 := rfl
  have hc7 : Nat.choose 37 7 = 10295472 := rfl
  have hs8 : 37 - 8 = 29 := rfl
  have hc8 : Nat.choose 37 8 = 38608020 := rfl
  have hs9 : 37 - 9 = 28 := rfl
  have hc9 : Nat.choose 37 9 = 124403620 := rfl
  have hs10 : 37 - 10 = 27 := rfl
  have hc10 : Nat.choose 37 10 = 348330136 := rfl
  have hs11 : 37 - 11 = 26 := rfl
  have hc11 : Nat.choose 37 11 = 854992152 := rfl
  have hs12 : 37 - 12 = 25 := rfl
  have hc12 : Nat.choose 37 12 = 1852482996 := rfl
  have hs13 : 37 - 13 = 24 := rfl
  have hc13 : Nat.choose 37 13 = 3562467300 := rfl
  have hs14 : 37 - 14 = 23 := rfl
  have hc14 : Nat.choose 37 14 = 6107086800 := rfl
  have hs15 : 37 - 15 = 22 := rfl
  have hc15 : Nat.choose 37 15 = 9364199760 := rfl
  have hs16 : 37 - 16 = 21 := rfl
  have hc16 : Nat.choose 37 16 = 12875774670 := rfl
  have hs17 : 37 - 17 = 20 := rfl
  have hc17 : Nat.choose 37 17 = 15905368710 := rfl
  have hs18 : 37 - 18 = 19 := rfl
  have hc18 : Nat.choose 37 18 = 17672631900 := rfl
  have hs19 : 37 - 19 = 18 := rfl
  have hc19 : Nat.choose 37 19 = 17672631900 := rfl
  have hs20 : 37 - 20 = 17 := rfl
  have hc20 : Nat.choose 37 20 = 15905368710 := rfl
  have hs21 : 37 - 21 = 16 := rfl
  have hc21 : Nat.choose 37 21 = 12875774670 := rfl
  have hs22 : 37 - 22 = 15 := rfl
  have hc22 : Nat.choose 37 22 = 9364199760 := rfl
  have hs23 : 37 - 23 = 14 := rfl
  have hc23 : Nat.choose 37 23 = 6107086800 := rfl
  have hs24 : 37 - 24 = 13 := rfl
  have hc24 : Nat.choose 37 24 = 3562467300 := rfl
  have hs25 : 37 - 25 = 12 := rfl
  have hc25 : Nat.choose 37 25 = 1852482996 := rfl
  have hs26 : 37 - 26 = 11 := rfl
  have hc26 : Nat.choose 37 26 = 854992152 := rfl
  have hs27 : 37 - 27 = 10 := rfl
  have hc27 : Nat.choose 37 27 = 348330136 := rfl
  have hs28 : 37 - 28 = 9 := rfl
  have hc28 : Nat.choose 37 28 = 124403620 := rfl
  have hs29 : 37 - 29 = 8 := rfl
  have hc29 : Nat.choose 37 29 = 38608020 := rfl
  have hs30 : 37 - 30 = 7 := rfl
  have hc30 : Nat.choose 37 30 = 10295472 := rfl
  have hs31 : 37 - 31 = 6 := rfl
  have hc31 : Nat.choose 37 31 = 2324784 := rfl
  have hs32 : 37 - 32 = 5 := rfl
  have hc32 : Nat.choose 37 32 = 435897 := rfl
  have hs33 : 37 - 33 = 4 := rfl
  have hc33 : Nat.choose 37 33 = 66045 := rfl
  have hs34 : 37 - 34 = 3 := rfl
  have hc34 : Nat.choose 37 34 = 7770 := rfl
  have hs35 : 37 - 35 = 2 := rfl
  have hc35 : Nat.choose 37 35 = 666 := rfl
  have hs36 : 37 - 36 = 1 := rfl
  have hc36 : Nat.choose 37 36 = 37 := rfl
  have hs37 : 37 - 37 = 0 := rfl
  have hc37 : Nat.choose 37 37 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_37 : A195441 (38 - 1) = 2730 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 38 - 0 = 38 := rfl
  have hc0 : Nat.choose 38 0 = 1 := rfl
  have hs1 : 38 - 1 = 37 := rfl
  have hc1 : Nat.choose 38 1 = 38 := rfl
  have hs2 : 38 - 2 = 36 := rfl
  have hc2 : Nat.choose 38 2 = 703 := rfl
  have hs3 : 38 - 3 = 35 := rfl
  have hc3 : Nat.choose 38 3 = 8436 := rfl
  have hs4 : 38 - 4 = 34 := rfl
  have hc4 : Nat.choose 38 4 = 73815 := rfl
  have hs5 : 38 - 5 = 33 := rfl
  have hc5 : Nat.choose 38 5 = 501942 := rfl
  have hs6 : 38 - 6 = 32 := rfl
  have hc6 : Nat.choose 38 6 = 2760681 := rfl
  have hs7 : 38 - 7 = 31 := rfl
  have hc7 : Nat.choose 38 7 = 12620256 := rfl
  have hs8 : 38 - 8 = 30 := rfl
  have hc8 : Nat.choose 38 8 = 48903492 := rfl
  have hs9 : 38 - 9 = 29 := rfl
  have hc9 : Nat.choose 38 9 = 163011640 := rfl
  have hs10 : 38 - 10 = 28 := rfl
  have hc10 : Nat.choose 38 10 = 472733756 := rfl
  have hs11 : 38 - 11 = 27 := rfl
  have hc11 : Nat.choose 38 11 = 1203322288 := rfl
  have hs12 : 38 - 12 = 26 := rfl
  have hc12 : Nat.choose 38 12 = 2707475148 := rfl
  have hs13 : 38 - 13 = 25 := rfl
  have hc13 : Nat.choose 38 13 = 5414950296 := rfl
  have hs14 : 38 - 14 = 24 := rfl
  have hc14 : Nat.choose 38 14 = 9669554100 := rfl
  have hs15 : 38 - 15 = 23 := rfl
  have hc15 : Nat.choose 38 15 = 15471286560 := rfl
  have hs16 : 38 - 16 = 22 := rfl
  have hc16 : Nat.choose 38 16 = 22239974430 := rfl
  have hs17 : 38 - 17 = 21 := rfl
  have hc17 : Nat.choose 38 17 = 28781143380 := rfl
  have hs18 : 38 - 18 = 20 := rfl
  have hc18 : Nat.choose 38 18 = 33578000610 := rfl
  have hs19 : 38 - 19 = 19 := rfl
  have hc19 : Nat.choose 38 19 = 35345263800 := rfl
  have hs20 : 38 - 20 = 18 := rfl
  have hc20 : Nat.choose 38 20 = 33578000610 := rfl
  have hs21 : 38 - 21 = 17 := rfl
  have hc21 : Nat.choose 38 21 = 28781143380 := rfl
  have hs22 : 38 - 22 = 16 := rfl
  have hc22 : Nat.choose 38 22 = 22239974430 := rfl
  have hs23 : 38 - 23 = 15 := rfl
  have hc23 : Nat.choose 38 23 = 15471286560 := rfl
  have hs24 : 38 - 24 = 14 := rfl
  have hc24 : Nat.choose 38 24 = 9669554100 := rfl
  have hs25 : 38 - 25 = 13 := rfl
  have hc25 : Nat.choose 38 25 = 5414950296 := rfl
  have hs26 : 38 - 26 = 12 := rfl
  have hc26 : Nat.choose 38 26 = 2707475148 := rfl
  have hs27 : 38 - 27 = 11 := rfl
  have hc27 : Nat.choose 38 27 = 1203322288 := rfl
  have hs28 : 38 - 28 = 10 := rfl
  have hc28 : Nat.choose 38 28 = 472733756 := rfl
  have hs29 : 38 - 29 = 9 := rfl
  have hc29 : Nat.choose 38 29 = 163011640 := rfl
  have hs30 : 38 - 30 = 8 := rfl
  have hc30 : Nat.choose 38 30 = 48903492 := rfl
  have hs31 : 38 - 31 = 7 := rfl
  have hc31 : Nat.choose 38 31 = 12620256 := rfl
  have hs32 : 38 - 32 = 6 := rfl
  have hc32 : Nat.choose 38 32 = 2760681 := rfl
  have hs33 : 38 - 33 = 5 := rfl
  have hc33 : Nat.choose 38 33 = 501942 := rfl
  have hs34 : 38 - 34 = 4 := rfl
  have hc34 : Nat.choose 38 34 = 73815 := rfl
  have hs35 : 38 - 35 = 3 := rfl
  have hc35 : Nat.choose 38 35 = 8436 := rfl
  have hs36 : 38 - 36 = 2 := rfl
  have hc36 : Nat.choose 38 36 = 703 := rfl
  have hs37 : 38 - 37 = 1 := rfl
  have hc37 : Nat.choose 38 37 = 38 := rfl
  have hs38 : 38 - 38 = 0 := rfl
  have hc38 : Nat.choose 38 38 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_38 : A195441 (39 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 39 - 0 = 39 := rfl
  have hc0 : Nat.choose 39 0 = 1 := rfl
  have hs1 : 39 - 1 = 38 := rfl
  have hc1 : Nat.choose 39 1 = 39 := rfl
  have hs2 : 39 - 2 = 37 := rfl
  have hc2 : Nat.choose 39 2 = 741 := rfl
  have hs3 : 39 - 3 = 36 := rfl
  have hc3 : Nat.choose 39 3 = 9139 := rfl
  have hs4 : 39 - 4 = 35 := rfl
  have hc4 : Nat.choose 39 4 = 82251 := rfl
  have hs5 : 39 - 5 = 34 := rfl
  have hc5 : Nat.choose 39 5 = 575757 := rfl
  have hs6 : 39 - 6 = 33 := rfl
  have hc6 : Nat.choose 39 6 = 3262623 := rfl
  have hs7 : 39 - 7 = 32 := rfl
  have hc7 : Nat.choose 39 7 = 15380937 := rfl
  have hs8 : 39 - 8 = 31 := rfl
  have hc8 : Nat.choose 39 8 = 61523748 := rfl
  have hs9 : 39 - 9 = 30 := rfl
  have hc9 : Nat.choose 39 9 = 211915132 := rfl
  have hs10 : 39 - 10 = 29 := rfl
  have hc10 : Nat.choose 39 10 = 635745396 := rfl
  have hs11 : 39 - 11 = 28 := rfl
  have hc11 : Nat.choose 39 11 = 1676056044 := rfl
  have hs12 : 39 - 12 = 27 := rfl
  have hc12 : Nat.choose 39 12 = 3910797436 := rfl
  have hs13 : 39 - 13 = 26 := rfl
  have hc13 : Nat.choose 39 13 = 8122425444 := rfl
  have hs14 : 39 - 14 = 25 := rfl
  have hc14 : Nat.choose 39 14 = 15084504396 := rfl
  have hs15 : 39 - 15 = 24 := rfl
  have hc15 : Nat.choose 39 15 = 25140840660 := rfl
  have hs16 : 39 - 16 = 23 := rfl
  have hc16 : Nat.choose 39 16 = 37711260990 := rfl
  have hs17 : 39 - 17 = 22 := rfl
  have hc17 : Nat.choose 39 17 = 51021117810 := rfl
  have hs18 : 39 - 18 = 21 := rfl
  have hc18 : Nat.choose 39 18 = 62359143990 := rfl
  have hs19 : 39 - 19 = 20 := rfl
  have hc19 : Nat.choose 39 19 = 68923264410 := rfl
  have hs20 : 39 - 20 = 19 := rfl
  have hc20 : Nat.choose 39 20 = 68923264410 := rfl
  have hs21 : 39 - 21 = 18 := rfl
  have hc21 : Nat.choose 39 21 = 62359143990 := rfl
  have hs22 : 39 - 22 = 17 := rfl
  have hc22 : Nat.choose 39 22 = 51021117810 := rfl
  have hs23 : 39 - 23 = 16 := rfl
  have hc23 : Nat.choose 39 23 = 37711260990 := rfl
  have hs24 : 39 - 24 = 15 := rfl
  have hc24 : Nat.choose 39 24 = 25140840660 := rfl
  have hs25 : 39 - 25 = 14 := rfl
  have hc25 : Nat.choose 39 25 = 15084504396 := rfl
  have hs26 : 39 - 26 = 13 := rfl
  have hc26 : Nat.choose 39 26 = 8122425444 := rfl
  have hs27 : 39 - 27 = 12 := rfl
  have hc27 : Nat.choose 39 27 = 3910797436 := rfl
  have hs28 : 39 - 28 = 11 := rfl
  have hc28 : Nat.choose 39 28 = 1676056044 := rfl
  have hs29 : 39 - 29 = 10 := rfl
  have hc29 : Nat.choose 39 29 = 635745396 := rfl
  have hs30 : 39 - 30 = 9 := rfl
  have hc30 : Nat.choose 39 30 = 211915132 := rfl
  have hs31 : 39 - 31 = 8 := rfl
  have hc31 : Nat.choose 39 31 = 61523748 := rfl
  have hs32 : 39 - 32 = 7 := rfl
  have hc32 : Nat.choose 39 32 = 15380937 := rfl
  have hs33 : 39 - 33 = 6 := rfl
  have hc33 : Nat.choose 39 33 = 3262623 := rfl
  have hs34 : 39 - 34 = 5 := rfl
  have hc34 : Nat.choose 39 34 = 575757 := rfl
  have hs35 : 39 - 35 = 4 := rfl
  have hc35 : Nat.choose 39 35 = 82251 := rfl
  have hs36 : 39 - 36 = 3 := rfl
  have hc36 : Nat.choose 39 36 = 9139 := rfl
  have hs37 : 39 - 37 = 2 := rfl
  have hc37 : Nat.choose 39 37 = 741 := rfl
  have hs38 : 39 - 38 = 1 := rfl
  have hc38 : Nat.choose 39 38 = 39 := rfl
  have hs39 : 39 - 39 = 0 := rfl
  have hc39 : Nat.choose 39 39 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_39 : A195441 (40 - 1) = 42 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 40 - 0 = 40 := rfl
  have hc0 : Nat.choose 40 0 = 1 := rfl
  have hs1 : 40 - 1 = 39 := rfl
  have hc1 : Nat.choose 40 1 = 40 := rfl
  have hs2 : 40 - 2 = 38 := rfl
  have hc2 : Nat.choose 40 2 = 780 := rfl
  have hs3 : 40 - 3 = 37 := rfl
  have hc3 : Nat.choose 40 3 = 9880 := rfl
  have hs4 : 40 - 4 = 36 := rfl
  have hc4 : Nat.choose 40 4 = 91390 := rfl
  have hs5 : 40 - 5 = 35 := rfl
  have hc5 : Nat.choose 40 5 = 658008 := rfl
  have hs6 : 40 - 6 = 34 := rfl
  have hc6 : Nat.choose 40 6 = 3838380 := rfl
  have hs7 : 40 - 7 = 33 := rfl
  have hc7 : Nat.choose 40 7 = 18643560 := rfl
  have hs8 : 40 - 8 = 32 := rfl
  have hc8 : Nat.choose 40 8 = 76904685 := rfl
  have hs9 : 40 - 9 = 31 := rfl
  have hc9 : Nat.choose 40 9 = 273438880 := rfl
  have hs10 : 40 - 10 = 30 := rfl
  have hc10 : Nat.choose 40 10 = 847660528 := rfl
  have hs11 : 40 - 11 = 29 := rfl
  have hc11 : Nat.choose 40 11 = 2311801440 := rfl
  have hs12 : 40 - 12 = 28 := rfl
  have hc12 : Nat.choose 40 12 = 5586853480 := rfl
  have hs13 : 40 - 13 = 27 := rfl
  have hc13 : Nat.choose 40 13 = 12033222880 := rfl
  have hs14 : 40 - 14 = 26 := rfl
  have hc14 : Nat.choose 40 14 = 23206929840 := rfl
  have hs15 : 40 - 15 = 25 := rfl
  have hc15 : Nat.choose 40 15 = 40225345056 := rfl
  have hs16 : 40 - 16 = 24 := rfl
  have hc16 : Nat.choose 40 16 = 62852101650 := rfl
  have hs17 : 40 - 17 = 23 := rfl
  have hc17 : Nat.choose 40 17 = 88732378800 := rfl
  have hs18 : 40 - 18 = 22 := rfl
  have hc18 : Nat.choose 40 18 = 113380261800 := rfl
  have hs19 : 40 - 19 = 21 := rfl
  have hc19 : Nat.choose 40 19 = 131282408400 := rfl
  have hs20 : 40 - 20 = 20 := rfl
  have hc20 : Nat.choose 40 20 = 137846528820 := rfl
  have hs21 : 40 - 21 = 19 := rfl
  have hc21 : Nat.choose 40 21 = 131282408400 := rfl
  have hs22 : 40 - 22 = 18 := rfl
  have hc22 : Nat.choose 40 22 = 113380261800 := rfl
  have hs23 : 40 - 23 = 17 := rfl
  have hc23 : Nat.choose 40 23 = 88732378800 := rfl
  have hs24 : 40 - 24 = 16 := rfl
  have hc24 : Nat.choose 40 24 = 62852101650 := rfl
  have hs25 : 40 - 25 = 15 := rfl
  have hc25 : Nat.choose 40 25 = 40225345056 := rfl
  have hs26 : 40 - 26 = 14 := rfl
  have hc26 : Nat.choose 40 26 = 23206929840 := rfl
  have hs27 : 40 - 27 = 13 := rfl
  have hc27 : Nat.choose 40 27 = 12033222880 := rfl
  have hs28 : 40 - 28 = 12 := rfl
  have hc28 : Nat.choose 40 28 = 5586853480 := rfl
  have hs29 : 40 - 29 = 11 := rfl
  have hc29 : Nat.choose 40 29 = 2311801440 := rfl
  have hs30 : 40 - 30 = 10 := rfl
  have hc30 : Nat.choose 40 30 = 847660528 := rfl
  have hs31 : 40 - 31 = 9 := rfl
  have hc31 : Nat.choose 40 31 = 273438880 := rfl
  have hs32 : 40 - 32 = 8 := rfl
  have hc32 : Nat.choose 40 32 = 76904685 := rfl
  have hs33 : 40 - 33 = 7 := rfl
  have hc33 : Nat.choose 40 33 = 18643560 := rfl
  have hs34 : 40 - 34 = 6 := rfl
  have hc34 : Nat.choose 40 34 = 3838380 := rfl
  have hs35 : 40 - 35 = 5 := rfl
  have hc35 : Nat.choose 40 35 = 658008 := rfl
  have hs36 : 40 - 36 = 4 := rfl
  have hc36 : Nat.choose 40 36 = 91390 := rfl
  have hs37 : 40 - 37 = 3 := rfl
  have hc37 : Nat.choose 40 37 = 9880 := rfl
  have hs38 : 40 - 38 = 2 := rfl
  have hc38 : Nat.choose 40 38 = 780 := rfl
  have hs39 : 40 - 39 = 1 := rfl
  have hc39 : Nat.choose 40 39 = 40 := rfl
  have hs40 : 40 - 40 = 0 := rfl
  have hc40 : Nat.choose 40 40 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_40 : A195441 (41 - 1) = 2310 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 41 - 0 = 41 := rfl
  have hc0 : Nat.choose 41 0 = 1 := rfl
  have hs1 : 41 - 1 = 40 := rfl
  have hc1 : Nat.choose 41 1 = 41 := rfl
  have hs2 : 41 - 2 = 39 := rfl
  have hc2 : Nat.choose 41 2 = 820 := rfl
  have hs3 : 41 - 3 = 38 := rfl
  have hc3 : Nat.choose 41 3 = 10660 := rfl
  have hs4 : 41 - 4 = 37 := rfl
  have hc4 : Nat.choose 41 4 = 101270 := rfl
  have hs5 : 41 - 5 = 36 := rfl
  have hc5 : Nat.choose 41 5 = 749398 := rfl
  have hs6 : 41 - 6 = 35 := rfl
  have hc6 : Nat.choose 41 6 = 4496388 := rfl
  have hs7 : 41 - 7 = 34 := rfl
  have hc7 : Nat.choose 41 7 = 22481940 := rfl
  have hs8 : 41 - 8 = 33 := rfl
  have hc8 : Nat.choose 41 8 = 95548245 := rfl
  have hs9 : 41 - 9 = 32 := rfl
  have hc9 : Nat.choose 41 9 = 350343565 := rfl
  have hs10 : 41 - 10 = 31 := rfl
  have hc10 : Nat.choose 41 10 = 1121099408 := rfl
  have hs11 : 41 - 11 = 30 := rfl
  have hc11 : Nat.choose 41 11 = 3159461968 := rfl
  have hs12 : 41 - 12 = 29 := rfl
  have hc12 : Nat.choose 41 12 = 7898654920 := rfl
  have hs13 : 41 - 13 = 28 := rfl
  have hc13 : Nat.choose 41 13 = 17620076360 := rfl
  have hs14 : 41 - 14 = 27 := rfl
  have hc14 : Nat.choose 41 14 = 35240152720 := rfl
  have hs15 : 41 - 15 = 26 := rfl
  have hc15 : Nat.choose 41 15 = 63432274896 := rfl
  have hs16 : 41 - 16 = 25 := rfl
  have hc16 : Nat.choose 41 16 = 103077446706 := rfl
  have hs17 : 41 - 17 = 24 := rfl
  have hc17 : Nat.choose 41 17 = 151584480450 := rfl
  have hs18 : 41 - 18 = 23 := rfl
  have hc18 : Nat.choose 41 18 = 202112640600 := rfl
  have hs19 : 41 - 19 = 22 := rfl
  have hc19 : Nat.choose 41 19 = 244662670200 := rfl
  have hs20 : 41 - 20 = 21 := rfl
  have hc20 : Nat.choose 41 20 = 269128937220 := rfl
  have hs21 : 41 - 21 = 20 := rfl
  have hc21 : Nat.choose 41 21 = 269128937220 := rfl
  have hs22 : 41 - 22 = 19 := rfl
  have hc22 : Nat.choose 41 22 = 244662670200 := rfl
  have hs23 : 41 - 23 = 18 := rfl
  have hc23 : Nat.choose 41 23 = 202112640600 := rfl
  have hs24 : 41 - 24 = 17 := rfl
  have hc24 : Nat.choose 41 24 = 151584480450 := rfl
  have hs25 : 41 - 25 = 16 := rfl
  have hc25 : Nat.choose 41 25 = 103077446706 := rfl
  have hs26 : 41 - 26 = 15 := rfl
  have hc26 : Nat.choose 41 26 = 63432274896 := rfl
  have hs27 : 41 - 27 = 14 := rfl
  have hc27 : Nat.choose 41 27 = 35240152720 := rfl
  have hs28 : 41 - 28 = 13 := rfl
  have hc28 : Nat.choose 41 28 = 17620076360 := rfl
  have hs29 : 41 - 29 = 12 := rfl
  have hc29 : Nat.choose 41 29 = 7898654920 := rfl
  have hs30 : 41 - 30 = 11 := rfl
  have hc30 : Nat.choose 41 30 = 3159461968 := rfl
  have hs31 : 41 - 31 = 10 := rfl
  have hc31 : Nat.choose 41 31 = 1121099408 := rfl
  have hs32 : 41 - 32 = 9 := rfl
  have hc32 : Nat.choose 41 32 = 350343565 := rfl
  have hs33 : 41 - 33 = 8 := rfl
  have hc33 : Nat.choose 41 33 = 95548245 := rfl
  have hs34 : 41 - 34 = 7 := rfl
  have hc34 : Nat.choose 41 34 = 22481940 := rfl
  have hs35 : 41 - 35 = 6 := rfl
  have hc35 : Nat.choose 41 35 = 4496388 := rfl
  have hs36 : 41 - 36 = 5 := rfl
  have hc36 : Nat.choose 41 36 = 749398 := rfl
  have hs37 : 41 - 37 = 4 := rfl
  have hc37 : Nat.choose 41 37 = 101270 := rfl
  have hs38 : 41 - 38 = 3 := rfl
  have hc38 : Nat.choose 41 38 = 10660 := rfl
  have hs39 : 41 - 39 = 2 := rfl
  have hc39 : Nat.choose 41 39 = 820 := rfl
  have hs40 : 41 - 40 = 1 := rfl
  have hc40 : Nat.choose 41 40 = 41 := rfl
  have hs41 : 41 - 41 = 0 := rfl
  have hc41 : Nat.choose 41 41 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_41 : A195441 (42 - 1) = 330 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 42 - 0 = 42 := rfl
  have hc0 : Nat.choose 42 0 = 1 := rfl
  have hs1 : 42 - 1 = 41 := rfl
  have hc1 : Nat.choose 42 1 = 42 := rfl
  have hs2 : 42 - 2 = 40 := rfl
  have hc2 : Nat.choose 42 2 = 861 := rfl
  have hs3 : 42 - 3 = 39 := rfl
  have hc3 : Nat.choose 42 3 = 11480 := rfl
  have hs4 : 42 - 4 = 38 := rfl
  have hc4 : Nat.choose 42 4 = 111930 := rfl
  have hs5 : 42 - 5 = 37 := rfl
  have hc5 : Nat.choose 42 5 = 850668 := rfl
  have hs6 : 42 - 6 = 36 := rfl
  have hc6 : Nat.choose 42 6 = 5245786 := rfl
  have hs7 : 42 - 7 = 35 := rfl
  have hc7 : Nat.choose 42 7 = 26978328 := rfl
  have hs8 : 42 - 8 = 34 := rfl
  have hc8 : Nat.choose 42 8 = 118030185 := rfl
  have hs9 : 42 - 9 = 33 := rfl
  have hc9 : Nat.choose 42 9 = 445891810 := rfl
  have hs10 : 42 - 10 = 32 := rfl
  have hc10 : Nat.choose 42 10 = 1471442973 := rfl
  have hs11 : 42 - 11 = 31 := rfl
  have hc11 : Nat.choose 42 11 = 4280561376 := rfl
  have hs12 : 42 - 12 = 30 := rfl
  have hc12 : Nat.choose 42 12 = 11058116888 := rfl
  have hs13 : 42 - 13 = 29 := rfl
  have hc13 : Nat.choose 42 13 = 25518731280 := rfl
  have hs14 : 42 - 14 = 28 := rfl
  have hc14 : Nat.choose 42 14 = 52860229080 := rfl
  have hs15 : 42 - 15 = 27 := rfl
  have hc15 : Nat.choose 42 15 = 98672427616 := rfl
  have hs16 : 42 - 16 = 26 := rfl
  have hc16 : Nat.choose 42 16 = 166509721602 := rfl
  have hs17 : 42 - 17 = 25 := rfl
  have hc17 : Nat.choose 42 17 = 254661927156 := rfl
  have hs18 : 42 - 18 = 24 := rfl
  have hc18 : Nat.choose 42 18 = 353697121050 := rfl
  have hs19 : 42 - 19 = 23 := rfl
  have hc19 : Nat.choose 42 19 = 446775310800 := rfl
  have hs20 : 42 - 20 = 22 := rfl
  have hc20 : Nat.choose 42 20 = 513791607420 := rfl
  have hs21 : 42 - 21 = 21 := rfl
  have hc21 : Nat.choose 42 21 = 538257874440 := rfl
  have hs22 : 42 - 22 = 20 := rfl
  have hc22 : Nat.choose 42 22 = 513791607420 := rfl
  have hs23 : 42 - 23 = 19 := rfl
  have hc23 : Nat.choose 42 23 = 446775310800 := rfl
  have hs24 : 42 - 24 = 18 := rfl
  have hc24 : Nat.choose 42 24 = 353697121050 := rfl
  have hs25 : 42 - 25 = 17 := rfl
  have hc25 : Nat.choose 42 25 = 254661927156 := rfl
  have hs26 : 42 - 26 = 16 := rfl
  have hc26 : Nat.choose 42 26 = 166509721602 := rfl
  have hs27 : 42 - 27 = 15 := rfl
  have hc27 : Nat.choose 42 27 = 98672427616 := rfl
  have hs28 : 42 - 28 = 14 := rfl
  have hc28 : Nat.choose 42 28 = 52860229080 := rfl
  have hs29 : 42 - 29 = 13 := rfl
  have hc29 : Nat.choose 42 29 = 25518731280 := rfl
  have hs30 : 42 - 30 = 12 := rfl
  have hc30 : Nat.choose 42 30 = 11058116888 := rfl
  have hs31 : 42 - 31 = 11 := rfl
  have hc31 : Nat.choose 42 31 = 4280561376 := rfl
  have hs32 : 42 - 32 = 10 := rfl
  have hc32 : Nat.choose 42 32 = 1471442973 := rfl
  have hs33 : 42 - 33 = 9 := rfl
  have hc33 : Nat.choose 42 33 = 445891810 := rfl
  have hs34 : 42 - 34 = 8 := rfl
  have hc34 : Nat.choose 42 34 = 118030185 := rfl
  have hs35 : 42 - 35 = 7 := rfl
  have hc35 : Nat.choose 42 35 = 26978328 := rfl
  have hs36 : 42 - 36 = 6 := rfl
  have hc36 : Nat.choose 42 36 = 5245786 := rfl
  have hs37 : 42 - 37 = 5 := rfl
  have hc37 : Nat.choose 42 37 = 850668 := rfl
  have hs38 : 42 - 38 = 4 := rfl
  have hc38 : Nat.choose 42 38 = 111930 := rfl
  have hs39 : 42 - 39 = 3 := rfl
  have hc39 : Nat.choose 42 39 = 11480 := rfl
  have hs40 : 42 - 40 = 2 := rfl
  have hc40 : Nat.choose 42 40 = 861 := rfl
  have hs41 : 42 - 41 = 1 := rfl
  have hc41 : Nat.choose 42 41 = 42 := rfl
  have hs42 : 42 - 42 = 0 := rfl
  have hc42 : Nat.choose 42 42 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_42 : A195441 (43 - 1) = 2310 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 43 - 0 = 43 := rfl
  have hc0 : Nat.choose 43 0 = 1 := rfl
  have hs1 : 43 - 1 = 42 := rfl
  have hc1 : Nat.choose 43 1 = 43 := rfl
  have hs2 : 43 - 2 = 41 := rfl
  have hc2 : Nat.choose 43 2 = 903 := rfl
  have hs3 : 43 - 3 = 40 := rfl
  have hc3 : Nat.choose 43 3 = 12341 := rfl
  have hs4 : 43 - 4 = 39 := rfl
  have hc4 : Nat.choose 43 4 = 123410 := rfl
  have hs5 : 43 - 5 = 38 := rfl
  have hc5 : Nat.choose 43 5 = 962598 := rfl
  have hs6 : 43 - 6 = 37 := rfl
  have hc6 : Nat.choose 43 6 = 6096454 := rfl
  have hs7 : 43 - 7 = 36 := rfl
  have hc7 : Nat.choose 43 7 = 32224114 := rfl
  have hs8 : 43 - 8 = 35 := rfl
  have hc8 : Nat.choose 43 8 = 145008513 := rfl
  have hs9 : 43 - 9 = 34 := rfl
  have hc9 : Nat.choose 43 9 = 563921995 := rfl
  have hs10 : 43 - 10 = 33 := rfl
  have hc10 : Nat.choose 43 10 = 1917334783 := rfl
  have hs11 : 43 - 11 = 32 := rfl
  have hc11 : Nat.choose 43 11 = 5752004349 := rfl
  have hs12 : 43 - 12 = 31 := rfl
  have hc12 : Nat.choose 43 12 = 15338678264 := rfl
  have hs13 : 43 - 13 = 30 := rfl
  have hc13 : Nat.choose 43 13 = 36576848168 := rfl
  have hs14 : 43 - 14 = 29 := rfl
  have hc14 : Nat.choose 43 14 = 78378960360 := rfl
  have hs15 : 43 - 15 = 28 := rfl
  have hc15 : Nat.choose 43 15 = 151532656696 := rfl
  have hs16 : 43 - 16 = 27 := rfl
  have hc16 : Nat.choose 43 16 = 265182149218 := rfl
  have hs17 : 43 - 17 = 26 := rfl
  have hc17 : Nat.choose 43 17 = 421171648758 := rfl
  have hs18 : 43 - 18 = 25 := rfl
  have hc18 : Nat.choose 43 18 = 608359048206 := rfl
  have hs19 : 43 - 19 = 24 := rfl
  have hc19 : Nat.choose 43 19 = 800472431850 := rfl
  have hs20 : 43 - 20 = 23 := rfl
  have hc20 : Nat.choose 43 20 = 960566918220 := rfl
  have hs21 : 43 - 21 = 22 := rfl
  have hc21 : Nat.choose 43 21 = 1052049481860 := rfl
  have hs22 : 43 - 22 = 21 := rfl
  have hc22 : Nat.choose 43 22 = 1052049481860 := rfl
  have hs23 : 43 - 23 = 20 := rfl
  have hc23 : Nat.choose 43 23 = 960566918220 := rfl
  have hs24 : 43 - 24 = 19 := rfl
  have hc24 : Nat.choose 43 24 = 800472431850 := rfl
  have hs25 : 43 - 25 = 18 := rfl
  have hc25 : Nat.choose 43 25 = 608359048206 := rfl
  have hs26 : 43 - 26 = 17 := rfl
  have hc26 : Nat.choose 43 26 = 421171648758 := rfl
  have hs27 : 43 - 27 = 16 := rfl
  have hc27 : Nat.choose 43 27 = 265182149218 := rfl
  have hs28 : 43 - 28 = 15 := rfl
  have hc28 : Nat.choose 43 28 = 151532656696 := rfl
  have hs29 : 43 - 29 = 14 := rfl
  have hc29 : Nat.choose 43 29 = 78378960360 := rfl
  have hs30 : 43 - 30 = 13 := rfl
  have hc30 : Nat.choose 43 30 = 36576848168 := rfl
  have hs31 : 43 - 31 = 12 := rfl
  have hc31 : Nat.choose 43 31 = 15338678264 := rfl
  have hs32 : 43 - 32 = 11 := rfl
  have hc32 : Nat.choose 43 32 = 5752004349 := rfl
  have hs33 : 43 - 33 = 10 := rfl
  have hc33 : Nat.choose 43 33 = 1917334783 := rfl
  have hs34 : 43 - 34 = 9 := rfl
  have hc34 : Nat.choose 43 34 = 563921995 := rfl
  have hs35 : 43 - 35 = 8 := rfl
  have hc35 : Nat.choose 43 35 = 145008513 := rfl
  have hs36 : 43 - 36 = 7 := rfl
  have hc36 : Nat.choose 43 36 = 32224114 := rfl
  have hs37 : 43 - 37 = 6 := rfl
  have hc37 : Nat.choose 43 37 = 6096454 := rfl
  have hs38 : 43 - 38 = 5 := rfl
  have hc38 : Nat.choose 43 38 = 962598 := rfl
  have hs39 : 43 - 39 = 4 := rfl
  have hc39 : Nat.choose 43 39 = 123410 := rfl
  have hs40 : 43 - 40 = 3 := rfl
  have hc40 : Nat.choose 43 40 = 12341 := rfl
  have hs41 : 43 - 41 = 2 := rfl
  have hc41 : Nat.choose 43 41 = 903 := rfl
  have hs42 : 43 - 42 = 1 := rfl
  have hc42 : Nat.choose 43 42 = 43 := rfl
  have hs43 : 43 - 43 = 0 := rfl
  have hc43 : Nat.choose 43 43 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_43 : A195441 (44 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 44 - 0 = 44 := rfl
  have hc0 : Nat.choose 44 0 = 1 := rfl
  have hs1 : 44 - 1 = 43 := rfl
  have hc1 : Nat.choose 44 1 = 44 := rfl
  have hs2 : 44 - 2 = 42 := rfl
  have hc2 : Nat.choose 44 2 = 946 := rfl
  have hs3 : 44 - 3 = 41 := rfl
  have hc3 : Nat.choose 44 3 = 13244 := rfl
  have hs4 : 44 - 4 = 40 := rfl
  have hc4 : Nat.choose 44 4 = 135751 := rfl
  have hs5 : 44 - 5 = 39 := rfl
  have hc5 : Nat.choose 44 5 = 1086008 := rfl
  have hs6 : 44 - 6 = 38 := rfl
  have hc6 : Nat.choose 44 6 = 7059052 := rfl
  have hs7 : 44 - 7 = 37 := rfl
  have hc7 : Nat.choose 44 7 = 38320568 := rfl
  have hs8 : 44 - 8 = 36 := rfl
  have hc8 : Nat.choose 44 8 = 177232627 := rfl
  have hs9 : 44 - 9 = 35 := rfl
  have hc9 : Nat.choose 44 9 = 708930508 := rfl
  have hs10 : 44 - 10 = 34 := rfl
  have hc10 : Nat.choose 44 10 = 2481256778 := rfl
  have hs11 : 44 - 11 = 33 := rfl
  have hc11 : Nat.choose 44 11 = 7669339132 := rfl
  have hs12 : 44 - 12 = 32 := rfl
  have hc12 : Nat.choose 44 12 = 21090682613 := rfl
  have hs13 : 44 - 13 = 31 := rfl
  have hc13 : Nat.choose 44 13 = 51915526432 := rfl
  have hs14 : 44 - 14 = 30 := rfl
  have hc14 : Nat.choose 44 14 = 114955808528 := rfl
  have hs15 : 44 - 15 = 29 := rfl
  have hc15 : Nat.choose 44 15 = 229911617056 := rfl
  have hs16 : 44 - 16 = 28 := rfl
  have hc16 : Nat.choose 44 16 = 416714805914 := rfl
  have hs17 : 44 - 17 = 27 := rfl
  have hc17 : Nat.choose 44 17 = 686353797976 := rfl
  have hs18 : 44 - 18 = 26 := rfl
  have hc18 : Nat.choose 44 18 = 1029530696964 := rfl
  have hs19 : 44 - 19 = 25 := rfl
  have hc19 : Nat.choose 44 19 = 1408831480056 := rfl
  have hs20 : 44 - 20 = 24 := rfl
  have hc20 : Nat.choose 44 20 = 1761039350070 := rfl
  have hs21 : 44 - 21 = 23 := rfl
  have hc21 : Nat.choose 44 21 = 2012616400080 := rfl
  have hs22 : 44 - 22 = 22 := rfl
  have hc22 : Nat.choose 44 22 = 2104098963720 := rfl
  have hs23 : 44 - 23 = 21 := rfl
  have hc23 : Nat.choose 44 23 = 2012616400080 := rfl
  have hs24 : 44 - 24 = 20 := rfl
  have hc24 : Nat.choose 44 24 = 1761039350070 := rfl
  have hs25 : 44 - 25 = 19 := rfl
  have hc25 : Nat.choose 44 25 = 1408831480056 := rfl
  have hs26 : 44 - 26 = 18 := rfl
  have hc26 : Nat.choose 44 26 = 1029530696964 := rfl
  have hs27 : 44 - 27 = 17 := rfl
  have hc27 : Nat.choose 44 27 = 686353797976 := rfl
  have hs28 : 44 - 28 = 16 := rfl
  have hc28 : Nat.choose 44 28 = 416714805914 := rfl
  have hs29 : 44 - 29 = 15 := rfl
  have hc29 : Nat.choose 44 29 = 229911617056 := rfl
  have hs30 : 44 - 30 = 14 := rfl
  have hc30 : Nat.choose 44 30 = 114955808528 := rfl
  have hs31 : 44 - 31 = 13 := rfl
  have hc31 : Nat.choose 44 31 = 51915526432 := rfl
  have hs32 : 44 - 32 = 12 := rfl
  have hc32 : Nat.choose 44 32 = 21090682613 := rfl
  have hs33 : 44 - 33 = 11 := rfl
  have hc33 : Nat.choose 44 33 = 7669339132 := rfl
  have hs34 : 44 - 34 = 10 := rfl
  have hc34 : Nat.choose 44 34 = 2481256778 := rfl
  have hs35 : 44 - 35 = 9 := rfl
  have hc35 : Nat.choose 44 35 = 708930508 := rfl
  have hs36 : 44 - 36 = 8 := rfl
  have hc36 : Nat.choose 44 36 = 177232627 := rfl
  have hs37 : 44 - 37 = 7 := rfl
  have hc37 : Nat.choose 44 37 = 38320568 := rfl
  have hs38 : 44 - 38 = 6 := rfl
  have hc38 : Nat.choose 44 38 = 7059052 := rfl
  have hs39 : 44 - 39 = 5 := rfl
  have hc39 : Nat.choose 44 39 = 1086008 := rfl
  have hs40 : 44 - 40 = 4 := rfl
  have hc40 : Nat.choose 44 40 = 135751 := rfl
  have hs41 : 44 - 41 = 3 := rfl
  have hc41 : Nat.choose 44 41 = 13244 := rfl
  have hs42 : 44 - 42 = 2 := rfl
  have hc42 : Nat.choose 44 42 = 946 := rfl
  have hs43 : 44 - 43 = 1 := rfl
  have hc43 : Nat.choose 44 43 = 44 := rfl
  have hs44 : 44 - 44 = 0 := rfl
  have hc44 : Nat.choose 44 44 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_44 : A195441 (45 - 1) = 4830 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 45 - 0 = 45 := rfl
  have hc0 : Nat.choose 45 0 = 1 := rfl
  have hs1 : 45 - 1 = 44 := rfl
  have hc1 : Nat.choose 45 1 = 45 := rfl
  have hs2 : 45 - 2 = 43 := rfl
  have hc2 : Nat.choose 45 2 = 990 := rfl
  have hs3 : 45 - 3 = 42 := rfl
  have hc3 : Nat.choose 45 3 = 14190 := rfl
  have hs4 : 45 - 4 = 41 := rfl
  have hc4 : Nat.choose 45 4 = 148995 := rfl
  have hs5 : 45 - 5 = 40 := rfl
  have hc5 : Nat.choose 45 5 = 1221759 := rfl
  have hs6 : 45 - 6 = 39 := rfl
  have hc6 : Nat.choose 45 6 = 8145060 := rfl
  have hs7 : 45 - 7 = 38 := rfl
  have hc7 : Nat.choose 45 7 = 45379620 := rfl
  have hs8 : 45 - 8 = 37 := rfl
  have hc8 : Nat.choose 45 8 = 215553195 := rfl
  have hs9 : 45 - 9 = 36 := rfl
  have hc9 : Nat.choose 45 9 = 886163135 := rfl
  have hs10 : 45 - 10 = 35 := rfl
  have hc10 : Nat.choose 45 10 = 3190187286 := rfl
  have hs11 : 45 - 11 = 34 := rfl
  have hc11 : Nat.choose 45 11 = 10150595910 := rfl
  have hs12 : 45 - 12 = 33 := rfl
  have hc12 : Nat.choose 45 12 = 28760021745 := rfl
  have hs13 : 45 - 13 = 32 := rfl
  have hc13 : Nat.choose 45 13 = 73006209045 := rfl
  have hs14 : 45 - 14 = 31 := rfl
  have hc14 : Nat.choose 45 14 = 166871334960 := rfl
  have hs15 : 45 - 15 = 30 := rfl
  have hc15 : Nat.choose 45 15 = 344867425584 := rfl
  have hs16 : 45 - 16 = 29 := rfl
  have hc16 : Nat.choose 45 16 = 646626422970 := rfl
  have hs17 : 45 - 17 = 28 := rfl
  have hc17 : Nat.choose 45 17 = 1103068603890 := rfl
  have hs18 : 45 - 18 = 27 := rfl
  have hc18 : Nat.choose 45 18 = 1715884494940 := rfl
  have hs19 : 45 - 19 = 26 := rfl
  have hc19 : Nat.choose 45 19 = 2438362177020 := rfl
  have hs20 : 45 - 20 = 25 := rfl
  have hc20 : Nat.choose 45 20 = 3169870830126 := rfl
  have hs21 : 45 - 21 = 24 := rfl
  have hc21 : Nat.choose 45 21 = 3773655750150 := rfl
  have hs22 : 45 - 22 = 23 := rfl
  have hc22 : Nat.choose 45 22 = 4116715363800 := rfl
  have hs23 : 45 - 23 = 22 := rfl
  have hc23 : Nat.choose 45 23 = 4116715363800 := rfl
  have hs24 : 45 - 24 = 21 := rfl
  have hc24 : Nat.choose 45 24 = 3773655750150 := rfl
  have hs25 : 45 - 25 = 20 := rfl
  have hc25 : Nat.choose 45 25 = 3169870830126 := rfl
  have hs26 : 45 - 26 = 19 := rfl
  have hc26 : Nat.choose 45 26 = 2438362177020 := rfl
  have hs27 : 45 - 27 = 18 := rfl
  have hc27 : Nat.choose 45 27 = 1715884494940 := rfl
  have hs28 : 45 - 28 = 17 := rfl
  have hc28 : Nat.choose 45 28 = 1103068603890 := rfl
  have hs29 : 45 - 29 = 16 := rfl
  have hc29 : Nat.choose 45 29 = 646626422970 := rfl
  have hs30 : 45 - 30 = 15 := rfl
  have hc30 : Nat.choose 45 30 = 344867425584 := rfl
  have hs31 : 45 - 31 = 14 := rfl
  have hc31 : Nat.choose 45 31 = 166871334960 := rfl
  have hs32 : 45 - 32 = 13 := rfl
  have hc32 : Nat.choose 45 32 = 73006209045 := rfl
  have hs33 : 45 - 33 = 12 := rfl
  have hc33 : Nat.choose 45 33 = 28760021745 := rfl
  have hs34 : 45 - 34 = 11 := rfl
  have hc34 : Nat.choose 45 34 = 10150595910 := rfl
  have hs35 : 45 - 35 = 10 := rfl
  have hc35 : Nat.choose 45 35 = 3190187286 := rfl
  have hs36 : 45 - 36 = 9 := rfl
  have hc36 : Nat.choose 45 36 = 886163135 := rfl
  have hs37 : 45 - 37 = 8 := rfl
  have hc37 : Nat.choose 45 37 = 215553195 := rfl
  have hs38 : 45 - 38 = 7 := rfl
  have hc38 : Nat.choose 45 38 = 45379620 := rfl
  have hs39 : 45 - 39 = 6 := rfl
  have hc39 : Nat.choose 45 39 = 8145060 := rfl
  have hs40 : 45 - 40 = 5 := rfl
  have hc40 : Nat.choose 45 40 = 1221759 := rfl
  have hs41 : 45 - 41 = 4 := rfl
  have hc41 : Nat.choose 45 41 = 148995 := rfl
  have hs42 : 45 - 42 = 3 := rfl
  have hc42 : Nat.choose 45 42 = 14190 := rfl
  have hs43 : 45 - 43 = 2 := rfl
  have hc43 : Nat.choose 45 43 = 990 := rfl
  have hs44 : 45 - 44 = 1 := rfl
  have hc44 : Nat.choose 45 44 = 45 := rfl
  have hs45 : 45 - 45 = 0 := rfl
  have hc45 : Nat.choose 45 45 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_45 : A195441 (46 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 46 - 0 = 46 := rfl
  have hc0 : Nat.choose 46 0 = 1 := rfl
  have hs1 : 46 - 1 = 45 := rfl
  have hc1 : Nat.choose 46 1 = 46 := rfl
  have hs2 : 46 - 2 = 44 := rfl
  have hc2 : Nat.choose 46 2 = 1035 := rfl
  have hs3 : 46 - 3 = 43 := rfl
  have hc3 : Nat.choose 46 3 = 15180 := rfl
  have hs4 : 46 - 4 = 42 := rfl
  have hc4 : Nat.choose 46 4 = 163185 := rfl
  have hs5 : 46 - 5 = 41 := rfl
  have hc5 : Nat.choose 46 5 = 1370754 := rfl
  have hs6 : 46 - 6 = 40 := rfl
  have hc6 : Nat.choose 46 6 = 9366819 := rfl
  have hs7 : 46 - 7 = 39 := rfl
  have hc7 : Nat.choose 46 7 = 53524680 := rfl
  have hs8 : 46 - 8 = 38 := rfl
  have hc8 : Nat.choose 46 8 = 260932815 := rfl
  have hs9 : 46 - 9 = 37 := rfl
  have hc9 : Nat.choose 46 9 = 1101716330 := rfl
  have hs10 : 46 - 10 = 36 := rfl
  have hc10 : Nat.choose 46 10 = 4076350421 := rfl
  have hs11 : 46 - 11 = 35 := rfl
  have hc11 : Nat.choose 46 11 = 13340783196 := rfl
  have hs12 : 46 - 12 = 34 := rfl
  have hc12 : Nat.choose 46 12 = 38910617655 := rfl
  have hs13 : 46 - 13 = 33 := rfl
  have hc13 : Nat.choose 46 13 = 101766230790 := rfl
  have hs14 : 46 - 14 = 32 := rfl
  have hc14 : Nat.choose 46 14 = 239877544005 := rfl
  have hs15 : 46 - 15 = 31 := rfl
  have hc15 : Nat.choose 46 15 = 511738760544 := rfl
  have hs16 : 46 - 16 = 30 := rfl
  have hc16 : Nat.choose 46 16 = 991493848554 := rfl
  have hs17 : 46 - 17 = 29 := rfl
  have hc17 : Nat.choose 46 17 = 1749695026860 := rfl
  have hs18 : 46 - 18 = 28 := rfl
  have hc18 : Nat.choose 46 18 = 2818953098830 := rfl
  have hs19 : 46 - 19 = 27 := rfl
  have hc19 : Nat.choose 46 19 = 4154246671960 := rfl
  have hs20 : 46 - 20 = 26 := rfl
  have hc20 : Nat.choose 46 20 = 5608233007146 := rfl
  have hs21 : 46 - 21 = 25 := rfl
  have hc21 : Nat.choose 46 21 = 6943526580276 := rfl
  have hs22 : 46 - 22 = 24 := rfl
  have hc22 : Nat.choose 46 22 = 7890371113950 := rfl
  have hs23 : 46 - 23 = 23 := rfl
  have hc23 : Nat.choose 46 23 = 8233430727600 := rfl
  have hs24 : 46 - 24 = 22 := rfl
  have hc24 : Nat.choose 46 24 = 7890371113950 := rfl
  have hs25 : 46 - 25 = 21 := rfl
  have hc25 : Nat.choose 46 25 = 6943526580276 := rfl
  have hs26 : 46 - 26 = 20 := rfl
  have hc26 : Nat.choose 46 26 = 5608233007146 := rfl
  have hs27 : 46 - 27 = 19 := rfl
  have hc27 : Nat.choose 46 27 = 4154246671960 := rfl
  have hs28 : 46 - 28 = 18 := rfl
  have hc28 : Nat.choose 46 28 = 2818953098830 := rfl
  have hs29 : 46 - 29 = 17 := rfl
  have hc29 : Nat.choose 46 29 = 1749695026860 := rfl
  have hs30 : 46 - 30 = 16 := rfl
  have hc30 : Nat.choose 46 30 = 991493848554 := rfl
  have hs31 : 46 - 31 = 15 := rfl
  have hc31 : Nat.choose 46 31 = 511738760544 := rfl
  have hs32 : 46 - 32 = 14 := rfl
  have hc32 : Nat.choose 46 32 = 239877544005 := rfl
  have hs33 : 46 - 33 = 13 := rfl
  have hc33 : Nat.choose 46 33 = 101766230790 := rfl
  have hs34 : 46 - 34 = 12 := rfl
  have hc34 : Nat.choose 46 34 = 38910617655 := rfl
  have hs35 : 46 - 35 = 11 := rfl
  have hc35 : Nat.choose 46 35 = 13340783196 := rfl
  have hs36 : 46 - 36 = 10 := rfl
  have hc36 : Nat.choose 46 36 = 4076350421 := rfl
  have hs37 : 46 - 37 = 9 := rfl
  have hc37 : Nat.choose 46 37 = 1101716330 := rfl
  have hs38 : 46 - 38 = 8 := rfl
  have hc38 : Nat.choose 46 38 = 260932815 := rfl
  have hs39 : 46 - 39 = 7 := rfl
  have hc39 : Nat.choose 46 39 = 53524680 := rfl
  have hs40 : 46 - 40 = 6 := rfl
  have hc40 : Nat.choose 46 40 = 9366819 := rfl
  have hs41 : 46 - 41 = 5 := rfl
  have hc41 : Nat.choose 46 41 = 1370754 := rfl
  have hs42 : 46 - 42 = 4 := rfl
  have hc42 : Nat.choose 46 42 = 163185 := rfl
  have hs43 : 46 - 43 = 3 := rfl
  have hc43 : Nat.choose 46 43 = 15180 := rfl
  have hs44 : 46 - 44 = 2 := rfl
  have hc44 : Nat.choose 46 44 = 1035 := rfl
  have hs45 : 46 - 45 = 1 := rfl
  have hc45 : Nat.choose 46 45 = 46 := rfl
  have hs46 : 46 - 46 = 0 := rfl
  have hc46 : Nat.choose 46 46 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_46 : A195441 (47 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 47 - 0 = 47 := rfl
  have hc0 : Nat.choose 47 0 = 1 := rfl
  have hs1 : 47 - 1 = 46 := rfl
  have hc1 : Nat.choose 47 1 = 47 := rfl
  have hs2 : 47 - 2 = 45 := rfl
  have hc2 : Nat.choose 47 2 = 1081 := rfl
  have hs3 : 47 - 3 = 44 := rfl
  have hc3 : Nat.choose 47 3 = 16215 := rfl
  have hs4 : 47 - 4 = 43 := rfl
  have hc4 : Nat.choose 47 4 = 178365 := rfl
  have hs5 : 47 - 5 = 42 := rfl
  have hc5 : Nat.choose 47 5 = 1533939 := rfl
  have hs6 : 47 - 6 = 41 := rfl
  have hc6 : Nat.choose 47 6 = 10737573 := rfl
  have hs7 : 47 - 7 = 40 := rfl
  have hc7 : Nat.choose 47 7 = 62891499 := rfl
  have hs8 : 47 - 8 = 39 := rfl
  have hc8 : Nat.choose 47 8 = 314457495 := rfl
  have hs9 : 47 - 9 = 38 := rfl
  have hc9 : Nat.choose 47 9 = 1362649145 := rfl
  have hs10 : 47 - 10 = 37 := rfl
  have hc10 : Nat.choose 47 10 = 5178066751 := rfl
  have hs11 : 47 - 11 = 36 := rfl
  have hc11 : Nat.choose 47 11 = 17417133617 := rfl
  have hs12 : 47 - 12 = 35 := rfl
  have hc12 : Nat.choose 47 12 = 52251400851 := rfl
  have hs13 : 47 - 13 = 34 := rfl
  have hc13 : Nat.choose 47 13 = 140676848445 := rfl
  have hs14 : 47 - 14 = 33 := rfl
  have hc14 : Nat.choose 47 14 = 341643774795 := rfl
  have hs15 : 47 - 15 = 32 := rfl
  have hc15 : Nat.choose 47 15 = 751616304549 := rfl
  have hs16 : 47 - 16 = 31 := rfl
  have hc16 : Nat.choose 47 16 = 1503232609098 := rfl
  have hs17 : 47 - 17 = 30 := rfl
  have hc17 : Nat.choose 47 17 = 2741188875414 := rfl
  have hs18 : 47 - 18 = 29 := rfl
  have hc18 : Nat.choose 47 18 = 4568648125690 := rfl
  have hs19 : 47 - 19 = 28 := rfl
  have hc19 : Nat.choose 47 19 = 6973199770790 := rfl
  have hs20 : 47 - 20 = 27 := rfl
  have hc20 : Nat.choose 47 20 = 9762479679106 := rfl
  have hs21 : 47 - 21 = 26 := rfl
  have hc21 : Nat.choose 47 21 = 12551759587422 := rfl
  have hs22 : 47 - 22 = 25 := rfl
  have hc22 : Nat.choose 47 22 = 14833897694226 := rfl
  have hs23 : 47 - 23 = 24 := rfl
  have hc23 : Nat.choose 47 23 = 16123801841550 := rfl
  have hs24 : 47 - 24 = 23 := rfl
  have hc24 : Nat.choose 47 24 = 16123801841550 := rfl
  have hs25 : 47 - 25 = 22 := rfl
  have hc25 : Nat.choose 47 25 = 14833897694226 := rfl
  have hs26 : 47 - 26 = 21 := rfl
  have hc26 : Nat.choose 47 26 = 12551759587422 := rfl
  have hs27 : 47 - 27 = 20 := rfl
  have hc27 : Nat.choose 47 27 = 9762479679106 := rfl
  have hs28 : 47 - 28 = 19 := rfl
  have hc28 : Nat.choose 47 28 = 6973199770790 := rfl
  have hs29 : 47 - 29 = 18 := rfl
  have hc29 : Nat.choose 47 29 = 4568648125690 := rfl
  have hs30 : 47 - 30 = 17 := rfl
  have hc30 : Nat.choose 47 30 = 2741188875414 := rfl
  have hs31 : 47 - 31 = 16 := rfl
  have hc31 : Nat.choose 47 31 = 1503232609098 := rfl
  have hs32 : 47 - 32 = 15 := rfl
  have hc32 : Nat.choose 47 32 = 751616304549 := rfl
  have hs33 : 47 - 33 = 14 := rfl
  have hc33 : Nat.choose 47 33 = 341643774795 := rfl
  have hs34 : 47 - 34 = 13 := rfl
  have hc34 : Nat.choose 47 34 = 140676848445 := rfl
  have hs35 : 47 - 35 = 12 := rfl
  have hc35 : Nat.choose 47 35 = 52251400851 := rfl
  have hs36 : 47 - 36 = 11 := rfl
  have hc36 : Nat.choose 47 36 = 17417133617 := rfl
  have hs37 : 47 - 37 = 10 := rfl
  have hc37 : Nat.choose 47 37 = 5178066751 := rfl
  have hs38 : 47 - 38 = 9 := rfl
  have hc38 : Nat.choose 47 38 = 1362649145 := rfl
  have hs39 : 47 - 39 = 8 := rfl
  have hc39 : Nat.choose 47 39 = 314457495 := rfl
  have hs40 : 47 - 40 = 7 := rfl
  have hc40 : Nat.choose 47 40 = 62891499 := rfl
  have hs41 : 47 - 41 = 6 := rfl
  have hc41 : Nat.choose 47 41 = 10737573 := rfl
  have hs42 : 47 - 42 = 5 := rfl
  have hc42 : Nat.choose 47 42 = 1533939 := rfl
  have hs43 : 47 - 43 = 4 := rfl
  have hc43 : Nat.choose 47 43 = 178365 := rfl
  have hs44 : 47 - 44 = 3 := rfl
  have hc44 : Nat.choose 47 44 = 16215 := rfl
  have hs45 : 47 - 45 = 2 := rfl
  have hc45 : Nat.choose 47 45 = 1081 := rfl
  have hs46 : 47 - 46 = 1 := rfl
  have hc46 : Nat.choose 47 46 = 47 := rfl
  have hs47 : 47 - 47 = 0 := rfl
  have hc47 : Nat.choose 47 47 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_47 : A195441 (48 - 1) = 210 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 48 - 0 = 48 := rfl
  have hc0 : Nat.choose 48 0 = 1 := rfl
  have hs1 : 48 - 1 = 47 := rfl
  have hc1 : Nat.choose 48 1 = 48 := rfl
  have hs2 : 48 - 2 = 46 := rfl
  have hc2 : Nat.choose 48 2 = 1128 := rfl
  have hs3 : 48 - 3 = 45 := rfl
  have hc3 : Nat.choose 48 3 = 17296 := rfl
  have hs4 : 48 - 4 = 44 := rfl
  have hc4 : Nat.choose 48 4 = 194580 := rfl
  have hs5 : 48 - 5 = 43 := rfl
  have hc5 : Nat.choose 48 5 = 1712304 := rfl
  have hs6 : 48 - 6 = 42 := rfl
  have hc6 : Nat.choose 48 6 = 12271512 := rfl
  have hs7 : 48 - 7 = 41 := rfl
  have hc7 : Nat.choose 48 7 = 73629072 := rfl
  have hs8 : 48 - 8 = 40 := rfl
  have hc8 : Nat.choose 48 8 = 377348994 := rfl
  have hs9 : 48 - 9 = 39 := rfl
  have hc9 : Nat.choose 48 9 = 1677106640 := rfl
  have hs10 : 48 - 10 = 38 := rfl
  have hc10 : Nat.choose 48 10 = 6540715896 := rfl
  have hs11 : 48 - 11 = 37 := rfl
  have hc11 : Nat.choose 48 11 = 22595200368 := rfl
  have hs12 : 48 - 12 = 36 := rfl
  have hc12 : Nat.choose 48 12 = 69668534468 := rfl
  have hs13 : 48 - 13 = 35 := rfl
  have hc13 : Nat.choose 48 13 = 192928249296 := rfl
  have hs14 : 48 - 14 = 34 := rfl
  have hc14 : Nat.choose 48 14 = 482320623240 := rfl
  have hs15 : 48 - 15 = 33 := rfl
  have hc15 : Nat.choose 48 15 = 1093260079344 := rfl
  have hs16 : 48 - 16 = 32 := rfl
  have hc16 : Nat.choose 48 16 = 2254848913647 := rfl
  have hs17 : 48 - 17 = 31 := rfl
  have hc17 : Nat.choose 48 17 = 4244421484512 := rfl
  have hs18 : 48 - 18 = 30 := rfl
  have hc18 : Nat.choose 48 18 = 7309837001104 := rfl
  have hs19 : 48 - 19 = 29 := rfl
  have hc19 : Nat.choose 48 19 = 11541847896480 := rfl
  have hs20 : 48 - 20 = 28 := rfl
  have hc20 : Nat.choose 48 20 = 16735679449896 := rfl
  have hs21 : 48 - 21 = 27 := rfl
  have hc21 : Nat.choose 48 21 = 22314239266528 := rfl
  have hs22 : 48 - 22 = 26 := rfl
  have hc22 : Nat.choose 48 22 = 27385657281648 := rfl
  have hs23 : 48 - 23 = 25 := rfl
  have hc23 : Nat.choose 48 23 = 30957699535776 := rfl
  have hs24 : 48 - 24 = 24 := rfl
  have hc24 : Nat.choose 48 24 = 32247603683100 := rfl
  have hs25 : 48 - 25 = 23 := rfl
  have hc25 : Nat.choose 48 25 = 30957699535776 := rfl
  have hs26 : 48 - 26 = 22 := rfl
  have hc26 : Nat.choose 48 26 = 27385657281648 := rfl
  have hs27 : 48 - 27 = 21 := rfl
  have hc27 : Nat.choose 48 27 = 22314239266528 := rfl
  have hs28 : 48 - 28 = 20 := rfl
  have hc28 : Nat.choose 48 28 = 16735679449896 := rfl
  have hs29 : 48 - 29 = 19 := rfl
  have hc29 : Nat.choose 48 29 = 11541847896480 := rfl
  have hs30 : 48 - 30 = 18 := rfl
  have hc30 : Nat.choose 48 30 = 7309837001104 := rfl
  have hs31 : 48 - 31 = 17 := rfl
  have hc31 : Nat.choose 48 31 = 4244421484512 := rfl
  have hs32 : 48 - 32 = 16 := rfl
  have hc32 : Nat.choose 48 32 = 2254848913647 := rfl
  have hs33 : 48 - 33 = 15 := rfl
  have hc33 : Nat.choose 48 33 = 1093260079344 := rfl
  have hs34 : 48 - 34 = 14 := rfl
  have hc34 : Nat.choose 48 34 = 482320623240 := rfl
  have hs35 : 48 - 35 = 13 := rfl
  have hc35 : Nat.choose 48 35 = 192928249296 := rfl
  have hs36 : 48 - 36 = 12 := rfl
  have hc36 : Nat.choose 48 36 = 69668534468 := rfl
  have hs37 : 48 - 37 = 11 := rfl
  have hc37 : Nat.choose 48 37 = 22595200368 := rfl
  have hs38 : 48 - 38 = 10 := rfl
  have hc38 : Nat.choose 48 38 = 6540715896 := rfl
  have hs39 : 48 - 39 = 9 := rfl
  have hc39 : Nat.choose 48 39 = 1677106640 := rfl
  have hs40 : 48 - 40 = 8 := rfl
  have hc40 : Nat.choose 48 40 = 377348994 := rfl
  have hs41 : 48 - 41 = 7 := rfl
  have hc41 : Nat.choose 48 41 = 73629072 := rfl
  have hs42 : 48 - 42 = 6 := rfl
  have hc42 : Nat.choose 48 42 = 12271512 := rfl
  have hs43 : 48 - 43 = 5 := rfl
  have hc43 : Nat.choose 48 43 = 1712304 := rfl
  have hs44 : 48 - 44 = 4 := rfl
  have hc44 : Nat.choose 48 44 = 194580 := rfl
  have hs45 : 48 - 45 = 3 := rfl
  have hc45 : Nat.choose 48 45 = 17296 := rfl
  have hs46 : 48 - 46 = 2 := rfl
  have hc46 : Nat.choose 48 46 = 1128 := rfl
  have hs47 : 48 - 47 = 1 := rfl
  have hc47 : Nat.choose 48 47 = 48 := rfl
  have hs48 : 48 - 48 = 0 := rfl
  have hc48 : Nat.choose 48 48 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_48 : A195441 (49 - 1) = 6630 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 49 - 0 = 49 := rfl
  have hc0 : Nat.choose 49 0 = 1 := rfl
  have hs1 : 49 - 1 = 48 := rfl
  have hc1 : Nat.choose 49 1 = 49 := rfl
  have hs2 : 49 - 2 = 47 := rfl
  have hc2 : Nat.choose 49 2 = 1176 := rfl
  have hs3 : 49 - 3 = 46 := rfl
  have hc3 : Nat.choose 49 3 = 18424 := rfl
  have hs4 : 49 - 4 = 45 := rfl
  have hc4 : Nat.choose 49 4 = 211876 := rfl
  have hs5 : 49 - 5 = 44 := rfl
  have hc5 : Nat.choose 49 5 = 1906884 := rfl
  have hs6 : 49 - 6 = 43 := rfl
  have hc6 : Nat.choose 49 6 = 13983816 := rfl
  have hs7 : 49 - 7 = 42 := rfl
  have hc7 : Nat.choose 49 7 = 85900584 := rfl
  have hs8 : 49 - 8 = 41 := rfl
  have hc8 : Nat.choose 49 8 = 450978066 := rfl
  have hs9 : 49 - 9 = 40 := rfl
  have hc9 : Nat.choose 49 9 = 2054455634 := rfl
  have hs10 : 49 - 10 = 39 := rfl
  have hc10 : Nat.choose 49 10 = 8217822536 := rfl
  have hs11 : 49 - 11 = 38 := rfl
  have hc11 : Nat.choose 49 11 = 29135916264 := rfl
  have hs12 : 49 - 12 = 37 := rfl
  have hc12 : Nat.choose 49 12 = 92263734836 := rfl
  have hs13 : 49 - 13 = 36 := rfl
  have hc13 : Nat.choose 49 13 = 262596783764 := rfl
  have hs14 : 49 - 14 = 35 := rfl
  have hc14 : Nat.choose 49 14 = 675248872536 := rfl
  have hs15 : 49 - 15 = 34 := rfl
  have hc15 : Nat.choose 49 15 = 1575580702584 := rfl
  have hs16 : 49 - 16 = 33 := rfl
  have hc16 : Nat.choose 49 16 = 3348108992991 := rfl
  have hs17 : 49 - 17 = 32 := rfl
  have hc17 : Nat.choose 49 17 = 6499270398159 := rfl
  have hs18 : 49 - 18 = 31 := rfl
  have hc18 : Nat.choose 49 18 = 11554258485616 := rfl
  have hs19 : 49 - 19 = 30 := rfl
  have hc19 : Nat.choose 49 19 = 18851684897584 := rfl
  have hs20 : 49 - 20 = 29 := rfl
  have hc20 : Nat.choose 49 20 = 28277527346376 := rfl
  have hs21 : 49 - 21 = 28 := rfl
  have hc21 : Nat.choose 49 21 = 39049918716424 := rfl
  have hs22 : 49 - 22 = 27 := rfl
  have hc22 : Nat.choose 49 22 = 49699896548176 := rfl
  have hs23 : 49 - 23 = 26 := rfl
  have hc23 : Nat.choose 49 23 = 58343356817424 := rfl
  have hs24 : 49 - 24 = 25 := rfl
  have hc24 : Nat.choose 49 24 = 63205303218876 := rfl
  have hs25 : 49 - 25 = 24 := rfl
  have hc25 : Nat.choose 49 25 = 63205303218876 := rfl
  have hs26 : 49 - 26 = 23 := rfl
  have hc26 : Nat.choose 49 26 = 58343356817424 := rfl
  have hs27 : 49 - 27 = 22 := rfl
  have hc27 : Nat.choose 49 27 = 49699896548176 := rfl
  have hs28 : 49 - 28 = 21 := rfl
  have hc28 : Nat.choose 49 28 = 39049918716424 := rfl
  have hs29 : 49 - 29 = 20 := rfl
  have hc29 : Nat.choose 49 29 = 28277527346376 := rfl
  have hs30 : 49 - 30 = 19 := rfl
  have hc30 : Nat.choose 49 30 = 18851684897584 := rfl
  have hs31 : 49 - 31 = 18 := rfl
  have hc31 : Nat.choose 49 31 = 11554258485616 := rfl
  have hs32 : 49 - 32 = 17 := rfl
  have hc32 : Nat.choose 49 32 = 6499270398159 := rfl
  have hs33 : 49 - 33 = 16 := rfl
  have hc33 : Nat.choose 49 33 = 3348108992991 := rfl
  have hs34 : 49 - 34 = 15 := rfl
  have hc34 : Nat.choose 49 34 = 1575580702584 := rfl
  have hs35 : 49 - 35 = 14 := rfl
  have hc35 : Nat.choose 49 35 = 675248872536 := rfl
  have hs36 : 49 - 36 = 13 := rfl
  have hc36 : Nat.choose 49 36 = 262596783764 := rfl
  have hs37 : 49 - 37 = 12 := rfl
  have hc37 : Nat.choose 49 37 = 92263734836 := rfl
  have hs38 : 49 - 38 = 11 := rfl
  have hc38 : Nat.choose 49 38 = 29135916264 := rfl
  have hs39 : 49 - 39 = 10 := rfl
  have hc39 : Nat.choose 49 39 = 8217822536 := rfl
  have hs40 : 49 - 40 = 9 := rfl
  have hc40 : Nat.choose 49 40 = 2054455634 := rfl
  have hs41 : 49 - 41 = 8 := rfl
  have hc41 : Nat.choose 49 41 = 450978066 := rfl
  have hs42 : 49 - 42 = 7 := rfl
  have hc42 : Nat.choose 49 42 = 85900584 := rfl
  have hs43 : 49 - 43 = 6 := rfl
  have hc43 : Nat.choose 49 43 = 13983816 := rfl
  have hs44 : 49 - 44 = 5 := rfl
  have hc44 : Nat.choose 49 44 = 1906884 := rfl
  have hs45 : 49 - 45 = 4 := rfl
  have hc45 : Nat.choose 49 45 = 211876 := rfl
  have hs46 : 49 - 46 = 3 := rfl
  have hc46 : Nat.choose 49 46 = 18424 := rfl
  have hs47 : 49 - 47 = 2 := rfl
  have hc47 : Nat.choose 49 47 = 1176 := rfl
  have hs48 : 49 - 48 = 1 := rfl
  have hc48 : Nat.choose 49 48 = 49 := rfl
  have hs49 : 49 - 49 = 0 := rfl
  have hc49 : Nat.choose 49 49 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_49 : A195441 (50 - 1) = 1326 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 50 - 0 = 50 := rfl
  have hc0 : Nat.choose 50 0 = 1 := rfl
  have hs1 : 50 - 1 = 49 := rfl
  have hc1 : Nat.choose 50 1 = 50 := rfl
  have hs2 : 50 - 2 = 48 := rfl
  have hc2 : Nat.choose 50 2 = 1225 := rfl
  have hs3 : 50 - 3 = 47 := rfl
  have hc3 : Nat.choose 50 3 = 19600 := rfl
  have hs4 : 50 - 4 = 46 := rfl
  have hc4 : Nat.choose 50 4 = 230300 := rfl
  have hs5 : 50 - 5 = 45 := rfl
  have hc5 : Nat.choose 50 5 = 2118760 := rfl
  have hs6 : 50 - 6 = 44 := rfl
  have hc6 : Nat.choose 50 6 = 15890700 := rfl
  have hs7 : 50 - 7 = 43 := rfl
  have hc7 : Nat.choose 50 7 = 99884400 := rfl
  have hs8 : 50 - 8 = 42 := rfl
  have hc8 : Nat.choose 50 8 = 536878650 := rfl
  have hs9 : 50 - 9 = 41 := rfl
  have hc9 : Nat.choose 50 9 = 2505433700 := rfl
  have hs10 : 50 - 10 = 40 := rfl
  have hc10 : Nat.choose 50 10 = 10272278170 := rfl
  have hs11 : 50 - 11 = 39 := rfl
  have hc11 : Nat.choose 50 11 = 37353738800 := rfl
  have hs12 : 50 - 12 = 38 := rfl
  have hc12 : Nat.choose 50 12 = 121399651100 := rfl
  have hs13 : 50 - 13 = 37 := rfl
  have hc13 : Nat.choose 50 13 = 354860518600 := rfl
  have hs14 : 50 - 14 = 36 := rfl
  have hc14 : Nat.choose 50 14 = 937845656300 := rfl
  have hs15 : 50 - 15 = 35 := rfl
  have hc15 : Nat.choose 50 15 = 2250829575120 := rfl
  have hs16 : 50 - 16 = 34 := rfl
  have hc16 : Nat.choose 50 16 = 4923689695575 := rfl
  have hs17 : 50 - 17 = 33 := rfl
  have hc17 : Nat.choose 50 17 = 9847379391150 := rfl
  have hs18 : 50 - 18 = 32 := rfl
  have hc18 : Nat.choose 50 18 = 18053528883775 := rfl
  have hs19 : 50 - 19 = 31 := rfl
  have hc19 : Nat.choose 50 19 = 30405943383200 := rfl
  have hs20 : 50 - 20 = 30 := rfl
  have hc20 : Nat.choose 50 20 = 47129212243960 := rfl
  have hs21 : 50 - 21 = 29 := rfl
  have hc21 : Nat.choose 50 21 = 67327446062800 := rfl
  have hs22 : 50 - 22 = 28 := rfl
  have hc22 : Nat.choose 50 22 = 88749815264600 := rfl
  have hs23 : 50 - 23 = 27 := rfl
  have hc23 : Nat.choose 50 23 = 108043253365600 := rfl
  have hs24 : 50 - 24 = 26 := rfl
  have hc24 : Nat.choose 50 24 = 121548660036300 := rfl
  have hs25 : 50 - 25 = 25 := rfl
  have hc25 : Nat.choose 50 25 = 126410606437752 := rfl
  have hs26 : 50 - 26 = 24 := rfl
  have hc26 : Nat.choose 50 26 = 121548660036300 := rfl
  have hs27 : 50 - 27 = 23 := rfl
  have hc27 : Nat.choose 50 27 = 108043253365600 := rfl
  have hs28 : 50 - 28 = 22 := rfl
  have hc28 : Nat.choose 50 28 = 88749815264600 := rfl
  have hs29 : 50 - 29 = 21 := rfl
  have hc29 : Nat.choose 50 29 = 67327446062800 := rfl
  have hs30 : 50 - 30 = 20 := rfl
  have hc30 : Nat.choose 50 30 = 47129212243960 := rfl
  have hs31 : 50 - 31 = 19 := rfl
  have hc31 : Nat.choose 50 31 = 30405943383200 := rfl
  have hs32 : 50 - 32 = 18 := rfl
  have hc32 : Nat.choose 50 32 = 18053528883775 := rfl
  have hs33 : 50 - 33 = 17 := rfl
  have hc33 : Nat.choose 50 33 = 9847379391150 := rfl
  have hs34 : 50 - 34 = 16 := rfl
  have hc34 : Nat.choose 50 34 = 4923689695575 := rfl
  have hs35 : 50 - 35 = 15 := rfl
  have hc35 : Nat.choose 50 35 = 2250829575120 := rfl
  have hs36 : 50 - 36 = 14 := rfl
  have hc36 : Nat.choose 50 36 = 937845656300 := rfl
  have hs37 : 50 - 37 = 13 := rfl
  have hc37 : Nat.choose 50 37 = 354860518600 := rfl
  have hs38 : 50 - 38 = 12 := rfl
  have hc38 : Nat.choose 50 38 = 121399651100 := rfl
  have hs39 : 50 - 39 = 11 := rfl
  have hc39 : Nat.choose 50 39 = 37353738800 := rfl
  have hs40 : 50 - 40 = 10 := rfl
  have hc40 : Nat.choose 50 40 = 10272278170 := rfl
  have hs41 : 50 - 41 = 9 := rfl
  have hc41 : Nat.choose 50 41 = 2505433700 := rfl
  have hs42 : 50 - 42 = 8 := rfl
  have hc42 : Nat.choose 50 42 = 536878650 := rfl
  have hs43 : 50 - 43 = 7 := rfl
  have hc43 : Nat.choose 50 43 = 99884400 := rfl
  have hs44 : 50 - 44 = 6 := rfl
  have hc44 : Nat.choose 50 44 = 15890700 := rfl
  have hs45 : 50 - 45 = 5 := rfl
  have hc45 : Nat.choose 50 45 = 2118760 := rfl
  have hs46 : 50 - 46 = 4 := rfl
  have hc46 : Nat.choose 50 46 = 230300 := rfl
  have hs47 : 50 - 47 = 3 := rfl
  have hc47 : Nat.choose 50 47 = 19600 := rfl
  have hs48 : 50 - 48 = 2 := rfl
  have hc48 : Nat.choose 50 48 = 1225 := rfl
  have hs49 : 50 - 49 = 1 := rfl
  have hc49 : Nat.choose 50 49 = 50 := rfl
  have hs50 : 50 - 50 = 0 := rfl
  have hc50 : Nat.choose 50 50 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_50 : A195441 (51 - 1) = 858 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 51 - 0 = 51 := rfl
  have hc0 : Nat.choose 51 0 = 1 := rfl
  have hs1 : 51 - 1 = 50 := rfl
  have hc1 : Nat.choose 51 1 = 51 := rfl
  have hs2 : 51 - 2 = 49 := rfl
  have hc2 : Nat.choose 51 2 = 1275 := rfl
  have hs3 : 51 - 3 = 48 := rfl
  have hc3 : Nat.choose 51 3 = 20825 := rfl
  have hs4 : 51 - 4 = 47 := rfl
  have hc4 : Nat.choose 51 4 = 249900 := rfl
  have hs5 : 51 - 5 = 46 := rfl
  have hc5 : Nat.choose 51 5 = 2349060 := rfl
  have hs6 : 51 - 6 = 45 := rfl
  have hc6 : Nat.choose 51 6 = 18009460 := rfl
  have hs7 : 51 - 7 = 44 := rfl
  have hc7 : Nat.choose 51 7 = 115775100 := rfl
  have hs8 : 51 - 8 = 43 := rfl
  have hc8 : Nat.choose 51 8 = 636763050 := rfl
  have hs9 : 51 - 9 = 42 := rfl
  have hc9 : Nat.choose 51 9 = 3042312350 := rfl
  have hs10 : 51 - 10 = 41 := rfl
  have hc10 : Nat.choose 51 10 = 12777711870 := rfl
  have hs11 : 51 - 11 = 40 := rfl
  have hc11 : Nat.choose 51 11 = 47626016970 := rfl
  have hs12 : 51 - 12 = 39 := rfl
  have hc12 : Nat.choose 51 12 = 158753389900 := rfl
  have hs13 : 51 - 13 = 38 := rfl
  have hc13 : Nat.choose 51 13 = 476260169700 := rfl
  have hs14 : 51 - 14 = 37 := rfl
  have hc14 : Nat.choose 51 14 = 1292706174900 := rfl
  have hs15 : 51 - 15 = 36 := rfl
  have hc15 : Nat.choose 51 15 = 3188675231420 := rfl
  have hs16 : 51 - 16 = 35 := rfl
  have hc16 : Nat.choose 51 16 = 7174519270695 := rfl
  have hs17 : 51 - 17 = 34 := rfl
  have hc17 : Nat.choose 51 17 = 14771069086725 := rfl
  have hs18 : 51 - 18 = 33 := rfl
  have hc18 : Nat.choose 51 18 = 27900908274925 := rfl
  have hs19 : 51 - 19 = 32 := rfl
  have hc19 : Nat.choose 51 19 = 48459472266975 := rfl
  have hs20 : 51 - 20 = 31 := rfl
  have hc20 : Nat.choose 51 20 = 77535155627160 := rfl
  have hs21 : 51 - 21 = 30 := rfl
  have hc21 : Nat.choose 51 21 = 114456658306760 := rfl
  have hs22 : 51 - 22 = 29 := rfl
  have hc22 : Nat.choose 51 22 = 156077261327400 := rfl
  have hs23 : 51 - 23 = 28 := rfl
  have hc23 : Nat.choose 51 23 = 196793068630200 := rfl
  have hs24 : 51 - 24 = 27 := rfl
  have hc24 : Nat.choose 51 24 = 229591913401900 := rfl
  have hs25 : 51 - 25 = 26 := rfl
  have hc25 : Nat.choose 51 25 = 247959266474052 := rfl
  have hs26 : 51 - 26 = 25 := rfl
  have hc26 : Nat.choose 51 26 = 247959266474052 := rfl
  have hs27 : 51 - 27 = 24 := rfl
  have hc27 : Nat.choose 51 27 = 229591913401900 := rfl
  have hs28 : 51 - 28 = 23 := rfl
  have hc28 : Nat.choose 51 28 = 196793068630200 := rfl
  have hs29 : 51 - 29 = 22 := rfl
  have hc29 : Nat.choose 51 29 = 156077261327400 := rfl
  have hs30 : 51 - 30 = 21 := rfl
  have hc30 : Nat.choose 51 30 = 114456658306760 := rfl
  have hs31 : 51 - 31 = 20 := rfl
  have hc31 : Nat.choose 51 31 = 77535155627160 := rfl
  have hs32 : 51 - 32 = 19 := rfl
  have hc32 : Nat.choose 51 32 = 48459472266975 := rfl
  have hs33 : 51 - 33 = 18 := rfl
  have hc33 : Nat.choose 51 33 = 27900908274925 := rfl
  have hs34 : 51 - 34 = 17 := rfl
  have hc34 : Nat.choose 51 34 = 14771069086725 := rfl
  have hs35 : 51 - 35 = 16 := rfl
  have hc35 : Nat.choose 51 35 = 7174519270695 := rfl
  have hs36 : 51 - 36 = 15 := rfl
  have hc36 : Nat.choose 51 36 = 3188675231420 := rfl
  have hs37 : 51 - 37 = 14 := rfl
  have hc37 : Nat.choose 51 37 = 1292706174900 := rfl
  have hs38 : 51 - 38 = 13 := rfl
  have hc38 : Nat.choose 51 38 = 476260169700 := rfl
  have hs39 : 51 - 39 = 12 := rfl
  have hc39 : Nat.choose 51 39 = 158753389900 := rfl
  have hs40 : 51 - 40 = 11 := rfl
  have hc40 : Nat.choose 51 40 = 47626016970 := rfl
  have hs41 : 51 - 41 = 10 := rfl
  have hc41 : Nat.choose 51 41 = 12777711870 := rfl
  have hs42 : 51 - 42 = 9 := rfl
  have hc42 : Nat.choose 51 42 = 3042312350 := rfl
  have hs43 : 51 - 43 = 8 := rfl
  have hc43 : Nat.choose 51 43 = 636763050 := rfl
  have hs44 : 51 - 44 = 7 := rfl
  have hc44 : Nat.choose 51 44 = 115775100 := rfl
  have hs45 : 51 - 45 = 6 := rfl
  have hc45 : Nat.choose 51 45 = 18009460 := rfl
  have hs46 : 51 - 46 = 5 := rfl
  have hc46 : Nat.choose 51 46 = 2349060 := rfl
  have hs47 : 51 - 47 = 4 := rfl
  have hc47 : Nat.choose 51 47 = 249900 := rfl
  have hs48 : 51 - 48 = 3 := rfl
  have hc48 : Nat.choose 51 48 = 20825 := rfl
  have hs49 : 51 - 49 = 2 := rfl
  have hc49 : Nat.choose 51 49 = 1275 := rfl
  have hs50 : 51 - 50 = 1 := rfl
  have hc50 : Nat.choose 51 50 = 51 := rfl
  have hs51 : 51 - 51 = 0 := rfl
  have hc51 : Nat.choose 51 51 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_51 : A195441 (52 - 1) = 66 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 52 - 0 = 52 := rfl
  have hc0 : Nat.choose 52 0 = 1 := rfl
  have hs1 : 52 - 1 = 51 := rfl
  have hc1 : Nat.choose 52 1 = 52 := rfl
  have hs2 : 52 - 2 = 50 := rfl
  have hc2 : Nat.choose 52 2 = 1326 := rfl
  have hs3 : 52 - 3 = 49 := rfl
  have hc3 : Nat.choose 52 3 = 22100 := rfl
  have hs4 : 52 - 4 = 48 := rfl
  have hc4 : Nat.choose 52 4 = 270725 := rfl
  have hs5 : 52 - 5 = 47 := rfl
  have hc5 : Nat.choose 52 5 = 2598960 := rfl
  have hs6 : 52 - 6 = 46 := rfl
  have hc6 : Nat.choose 52 6 = 20358520 := rfl
  have hs7 : 52 - 7 = 45 := rfl
  have hc7 : Nat.choose 52 7 = 133784560 := rfl
  have hs8 : 52 - 8 = 44 := rfl
  have hc8 : Nat.choose 52 8 = 752538150 := rfl
  have hs9 : 52 - 9 = 43 := rfl
  have hc9 : Nat.choose 52 9 = 3679075400 := rfl
  have hs10 : 52 - 10 = 42 := rfl
  have hc10 : Nat.choose 52 10 = 15820024220 := rfl
  have hs11 : 52 - 11 = 41 := rfl
  have hc11 : Nat.choose 52 11 = 60403728840 := rfl
  have hs12 : 52 - 12 = 40 := rfl
  have hc12 : Nat.choose 52 12 = 206379406870 := rfl
  have hs13 : 52 - 13 = 39 := rfl
  have hc13 : Nat.choose 52 13 = 635013559600 := rfl
  have hs14 : 52 - 14 = 38 := rfl
  have hc14 : Nat.choose 52 14 = 1768966344600 := rfl
  have hs15 : 52 - 15 = 37 := rfl
  have hc15 : Nat.choose 52 15 = 4481381406320 := rfl
  have hs16 : 52 - 16 = 36 := rfl
  have hc16 : Nat.choose 52 16 = 10363194502115 := rfl
  have hs17 : 52 - 17 = 35 := rfl
  have hc17 : Nat.choose 52 17 = 21945588357420 := rfl
  have hs18 : 52 - 18 = 34 := rfl
  have hc18 : Nat.choose 52 18 = 42671977361650 := rfl
  have hs19 : 52 - 19 = 33 := rfl
  have hc19 : Nat.choose 52 19 = 76360380541900 := rfl
  have hs20 : 52 - 20 = 32 := rfl
  have hc20 : Nat.choose 52 20 = 125994627894135 := rfl
  have hs21 : 52 - 21 = 31 := rfl
  have hc21 : Nat.choose 52 21 = 191991813933920 := rfl
  have hs22 : 52 - 22 = 30 := rfl
  have hc22 : Nat.choose 52 22 = 270533919634160 := rfl
  have hs23 : 52 - 23 = 29 := rfl
  have hc23 : Nat.choose 52 23 = 352870329957600 := rfl
  have hs24 : 52 - 24 = 28 := rfl
  have hc24 : Nat.choose 52 24 = 426384982032100 := rfl
  have hs25 : 52 - 25 = 27 := rfl
  have hc25 : Nat.choose 52 25 = 477551179875952 := rfl
  have hs26 : 52 - 26 = 26 := rfl
  have hc26 : Nat.choose 52 26 = 495918532948104 := rfl
  have hs27 : 52 - 27 = 25 := rfl
  have hc27 : Nat.choose 52 27 = 477551179875952 := rfl
  have hs28 : 52 - 28 = 24 := rfl
  have hc28 : Nat.choose 52 28 = 426384982032100 := rfl
  have hs29 : 52 - 29 = 23 := rfl
  have hc29 : Nat.choose 52 29 = 352870329957600 := rfl
  have hs30 : 52 - 30 = 22 := rfl
  have hc30 : Nat.choose 52 30 = 270533919634160 := rfl
  have hs31 : 52 - 31 = 21 := rfl
  have hc31 : Nat.choose 52 31 = 191991813933920 := rfl
  have hs32 : 52 - 32 = 20 := rfl
  have hc32 : Nat.choose 52 32 = 125994627894135 := rfl
  have hs33 : 52 - 33 = 19 := rfl
  have hc33 : Nat.choose 52 33 = 76360380541900 := rfl
  have hs34 : 52 - 34 = 18 := rfl
  have hc34 : Nat.choose 52 34 = 42671977361650 := rfl
  have hs35 : 52 - 35 = 17 := rfl
  have hc35 : Nat.choose 52 35 = 21945588357420 := rfl
  have hs36 : 52 - 36 = 16 := rfl
  have hc36 : Nat.choose 52 36 = 10363194502115 := rfl
  have hs37 : 52 - 37 = 15 := rfl
  have hc37 : Nat.choose 52 37 = 4481381406320 := rfl
  have hs38 : 52 - 38 = 14 := rfl
  have hc38 : Nat.choose 52 38 = 1768966344600 := rfl
  have hs39 : 52 - 39 = 13 := rfl
  have hc39 : Nat.choose 52 39 = 635013559600 := rfl
  have hs40 : 52 - 40 = 12 := rfl
  have hc40 : Nat.choose 52 40 = 206379406870 := rfl
  have hs41 : 52 - 41 = 11 := rfl
  have hc41 : Nat.choose 52 41 = 60403728840 := rfl
  have hs42 : 52 - 42 = 10 := rfl
  have hc42 : Nat.choose 52 42 = 15820024220 := rfl
  have hs43 : 52 - 43 = 9 := rfl
  have hc43 : Nat.choose 52 43 = 3679075400 := rfl
  have hs44 : 52 - 44 = 8 := rfl
  have hc44 : Nat.choose 52 44 = 752538150 := rfl
  have hs45 : 52 - 45 = 7 := rfl
  have hc45 : Nat.choose 52 45 = 133784560 := rfl
  have hs46 : 52 - 46 = 6 := rfl
  have hc46 : Nat.choose 52 46 = 20358520 := rfl
  have hs47 : 52 - 47 = 5 := rfl
  have hc47 : Nat.choose 52 47 = 2598960 := rfl
  have hs48 : 52 - 48 = 4 := rfl
  have hc48 : Nat.choose 52 48 = 270725 := rfl
  have hs49 : 52 - 49 = 3 := rfl
  have hc49 : Nat.choose 52 49 = 22100 := rfl
  have hs50 : 52 - 50 = 2 := rfl
  have hc50 : Nat.choose 52 50 = 1326 := rfl
  have hs51 : 52 - 51 = 1 := rfl
  have hc51 : Nat.choose 52 51 = 52 := rfl
  have hs52 : 52 - 52 = 0 := rfl
  have hc52 : Nat.choose 52 52 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_52 : A195441 (53 - 1) = 330 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 53 - 0 = 53 := rfl
  have hc0 : Nat.choose 53 0 = 1 := rfl
  have hs1 : 53 - 1 = 52 := rfl
  have hc1 : Nat.choose 53 1 = 53 := rfl
  have hs2 : 53 - 2 = 51 := rfl
  have hc2 : Nat.choose 53 2 = 1378 := rfl
  have hs3 : 53 - 3 = 50 := rfl
  have hc3 : Nat.choose 53 3 = 23426 := rfl
  have hs4 : 53 - 4 = 49 := rfl
  have hc4 : Nat.choose 53 4 = 292825 := rfl
  have hs5 : 53 - 5 = 48 := rfl
  have hc5 : Nat.choose 53 5 = 2869685 := rfl
  have hs6 : 53 - 6 = 47 := rfl
  have hc6 : Nat.choose 53 6 = 22957480 := rfl
  have hs7 : 53 - 7 = 46 := rfl
  have hc7 : Nat.choose 53 7 = 154143080 := rfl
  have hs8 : 53 - 8 = 45 := rfl
  have hc8 : Nat.choose 53 8 = 886322710 := rfl
  have hs9 : 53 - 9 = 44 := rfl
  have hc9 : Nat.choose 53 9 = 4431613550 := rfl
  have hs10 : 53 - 10 = 43 := rfl
  have hc10 : Nat.choose 53 10 = 19499099620 := rfl
  have hs11 : 53 - 11 = 42 := rfl
  have hc11 : Nat.choose 53 11 = 76223753060 := rfl
  have hs12 : 53 - 12 = 41 := rfl
  have hc12 : Nat.choose 53 12 = 266783135710 := rfl
  have hs13 : 53 - 13 = 40 := rfl
  have hc13 : Nat.choose 53 13 = 841392966470 := rfl
  have hs14 : 53 - 14 = 39 := rfl
  have hc14 : Nat.choose 53 14 = 2403979904200 := rfl
  have hs15 : 53 - 15 = 38 := rfl
  have hc15 : Nat.choose 53 15 = 6250347750920 := rfl
  have hs16 : 53 - 16 = 37 := rfl
  have hc16 : Nat.choose 53 16 = 14844575908435 := rfl
  have hs17 : 53 - 17 = 36 := rfl
  have hc17 : Nat.choose 53 17 = 32308782859535 := rfl
  have hs18 : 53 - 18 = 35 := rfl
  have hc18 : Nat.choose 53 18 = 64617565719070 := rfl
  have hs19 : 53 - 19 = 34 := rfl
  have hc19 : Nat.choose 53 19 = 119032357903550 := rfl
  have hs20 : 53 - 20 = 33 := rfl
  have hc20 : Nat.choose 53 20 = 202355008436035 := rfl
  have hs21 : 53 - 21 = 32 := rfl
  have hc21 : Nat.choose 53 21 = 317986441828055 := rfl
  have hs22 : 53 - 22 = 31 := rfl
  have hc22 : Nat.choose 53 22 = 462525733568080 := rfl
  have hs23 : 53 - 23 = 30 := rfl
  have hc23 : Nat.choose 53 23 = 623404249591760 := rfl
  have hs24 : 53 - 24 = 29 := rfl
  have hc24 : Nat.choose 53 24 = 779255311989700 := rfl
  have hs25 : 53 - 25 = 28 := rfl
  have hc25 : Nat.choose 53 25 = 903936161908052 := rfl
  have hs26 : 53 - 26 = 27 := rfl
  have hc26 : Nat.choose 53 26 = 973469712824056 := rfl
  have hs27 : 53 - 27 = 26 := rfl
  have hc27 : Nat.choose 53 27 = 973469712824056 := rfl
  have hs28 : 53 - 28 = 25 := rfl
  have hc28 : Nat.choose 53 28 = 903936161908052 := rfl
  have hs29 : 53 - 29 = 24 := rfl
  have hc29 : Nat.choose 53 29 = 779255311989700 := rfl
  have hs30 : 53 - 30 = 23 := rfl
  have hc30 : Nat.choose 53 30 = 623404249591760 := rfl
  have hs31 : 53 - 31 = 22 := rfl
  have hc31 : Nat.choose 53 31 = 462525733568080 := rfl
  have hs32 : 53 - 32 = 21 := rfl
  have hc32 : Nat.choose 53 32 = 317986441828055 := rfl
  have hs33 : 53 - 33 = 20 := rfl
  have hc33 : Nat.choose 53 33 = 202355008436035 := rfl
  have hs34 : 53 - 34 = 19 := rfl
  have hc34 : Nat.choose 53 34 = 119032357903550 := rfl
  have hs35 : 53 - 35 = 18 := rfl
  have hc35 : Nat.choose 53 35 = 64617565719070 := rfl
  have hs36 : 53 - 36 = 17 := rfl
  have hc36 : Nat.choose 53 36 = 32308782859535 := rfl
  have hs37 : 53 - 37 = 16 := rfl
  have hc37 : Nat.choose 53 37 = 14844575908435 := rfl
  have hs38 : 53 - 38 = 15 := rfl
  have hc38 : Nat.choose 53 38 = 6250347750920 := rfl
  have hs39 : 53 - 39 = 14 := rfl
  have hc39 : Nat.choose 53 39 = 2403979904200 := rfl
  have hs40 : 53 - 40 = 13 := rfl
  have hc40 : Nat.choose 53 40 = 841392966470 := rfl
  have hs41 : 53 - 41 = 12 := rfl
  have hc41 : Nat.choose 53 41 = 266783135710 := rfl
  have hs42 : 53 - 42 = 11 := rfl
  have hc42 : Nat.choose 53 42 = 76223753060 := rfl
  have hs43 : 53 - 43 = 10 := rfl
  have hc43 : Nat.choose 53 43 = 19499099620 := rfl
  have hs44 : 53 - 44 = 9 := rfl
  have hc44 : Nat.choose 53 44 = 4431613550 := rfl
  have hs45 : 53 - 45 = 8 := rfl
  have hc45 : Nat.choose 53 45 = 886322710 := rfl
  have hs46 : 53 - 46 = 7 := rfl
  have hc46 : Nat.choose 53 46 = 154143080 := rfl
  have hs47 : 53 - 47 = 6 := rfl
  have hc47 : Nat.choose 53 47 = 22957480 := rfl
  have hs48 : 53 - 48 = 5 := rfl
  have hc48 : Nat.choose 53 48 = 2869685 := rfl
  have hs49 : 53 - 49 = 4 := rfl
  have hc49 : Nat.choose 53 49 = 292825 := rfl
  have hs50 : 53 - 50 = 3 := rfl
  have hc50 : Nat.choose 53 50 = 23426 := rfl
  have hs51 : 53 - 51 = 2 := rfl
  have hc51 : Nat.choose 53 51 = 1378 := rfl
  have hs52 : 53 - 52 = 1 := rfl
  have hc52 : Nat.choose 53 52 = 53 := rfl
  have hs53 : 53 - 53 = 0 := rfl
  have hc53 : Nat.choose 53 53 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_53 : A195441 (54 - 1) = 110 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 54 - 0 = 54 := rfl
  have hc0 : Nat.choose 54 0 = 1 := rfl
  have hs1 : 54 - 1 = 53 := rfl
  have hc1 : Nat.choose 54 1 = 54 := rfl
  have hs2 : 54 - 2 = 52 := rfl
  have hc2 : Nat.choose 54 2 = 1431 := rfl
  have hs3 : 54 - 3 = 51 := rfl
  have hc3 : Nat.choose 54 3 = 24804 := rfl
  have hs4 : 54 - 4 = 50 := rfl
  have hc4 : Nat.choose 54 4 = 316251 := rfl
  have hs5 : 54 - 5 = 49 := rfl
  have hc5 : Nat.choose 54 5 = 3162510 := rfl
  have hs6 : 54 - 6 = 48 := rfl
  have hc6 : Nat.choose 54 6 = 25827165 := rfl
  have hs7 : 54 - 7 = 47 := rfl
  have hc7 : Nat.choose 54 7 = 177100560 := rfl
  have hs8 : 54 - 8 = 46 := rfl
  have hc8 : Nat.choose 54 8 = 1040465790 := rfl
  have hs9 : 54 - 9 = 45 := rfl
  have hc9 : Nat.choose 54 9 = 5317936260 := rfl
  have hs10 : 54 - 10 = 44 := rfl
  have hc10 : Nat.choose 54 10 = 23930713170 := rfl
  have hs11 : 54 - 11 = 43 := rfl
  have hc11 : Nat.choose 54 11 = 95722852680 := rfl
  have hs12 : 54 - 12 = 42 := rfl
  have hc12 : Nat.choose 54 12 = 343006888770 := rfl
  have hs13 : 54 - 13 = 41 := rfl
  have hc13 : Nat.choose 54 13 = 1108176102180 := rfl
  have hs14 : 54 - 14 = 40 := rfl
  have hc14 : Nat.choose 54 14 = 3245372870670 := rfl
  have hs15 : 54 - 15 = 39 := rfl
  have hc15 : Nat.choose 54 15 = 8654327655120 := rfl
  have hs16 : 54 - 16 = 38 := rfl
  have hc16 : Nat.choose 54 16 = 21094923659355 := rfl
  have hs17 : 54 - 17 = 37 := rfl
  have hc17 : Nat.choose 54 17 = 47153358767970 := rfl
  have hs18 : 54 - 18 = 36 := rfl
  have hc18 : Nat.choose 54 18 = 96926348578605 := rfl
  have hs19 : 54 - 19 = 35 := rfl
  have hc19 : Nat.choose 54 19 = 183649923622620 := rfl
  have hs20 : 54 - 20 = 34 := rfl
  have hc20 : Nat.choose 54 20 = 321387366339585 := rfl
  have hs21 : 54 - 21 = 33 := rfl
  have hc21 : Nat.choose 54 21 = 520341450264090 := rfl
  have hs22 : 54 - 22 = 32 := rfl
  have hc22 : Nat.choose 54 22 = 780512175396135 := rfl
  have hs23 : 54 - 23 = 31 := rfl
  have hc23 : Nat.choose 54 23 = 1085929983159840 := rfl
  have hs24 : 54 - 24 = 30 := rfl
  have hc24 : Nat.choose 54 24 = 1402659561581460 := rfl
  have hs25 : 54 - 25 = 29 := rfl
  have hc25 : Nat.choose 54 25 = 1683191473897752 := rfl
  have hs26 : 54 - 26 = 28 := rfl
  have hc26 : Nat.choose 54 26 = 1877405874732108 := rfl
  have hs27 : 54 - 27 = 27 := rfl
  have hc27 : Nat.choose 54 27 = 1946939425648112 := rfl
  have hs28 : 54 - 28 = 26 := rfl
  have hc28 : Nat.choose 54 28 = 1877405874732108 := rfl
  have hs29 : 54 - 29 = 25 := rfl
  have hc29 : Nat.choose 54 29 = 1683191473897752 := rfl
  have hs30 : 54 - 30 = 24 := rfl
  have hc30 : Nat.choose 54 30 = 1402659561581460 := rfl
  have hs31 : 54 - 31 = 23 := rfl
  have hc31 : Nat.choose 54 31 = 1085929983159840 := rfl
  have hs32 : 54 - 32 = 22 := rfl
  have hc32 : Nat.choose 54 32 = 780512175396135 := rfl
  have hs33 : 54 - 33 = 21 := rfl
  have hc33 : Nat.choose 54 33 = 520341450264090 := rfl
  have hs34 : 54 - 34 = 20 := rfl
  have hc34 : Nat.choose 54 34 = 321387366339585 := rfl
  have hs35 : 54 - 35 = 19 := rfl
  have hc35 : Nat.choose 54 35 = 183649923622620 := rfl
  have hs36 : 54 - 36 = 18 := rfl
  have hc36 : Nat.choose 54 36 = 96926348578605 := rfl
  have hs37 : 54 - 37 = 17 := rfl
  have hc37 : Nat.choose 54 37 = 47153358767970 := rfl
  have hs38 : 54 - 38 = 16 := rfl
  have hc38 : Nat.choose 54 38 = 21094923659355 := rfl
  have hs39 : 54 - 39 = 15 := rfl
  have hc39 : Nat.choose 54 39 = 8654327655120 := rfl
  have hs40 : 54 - 40 = 14 := rfl
  have hc40 : Nat.choose 54 40 = 3245372870670 := rfl
  have hs41 : 54 - 41 = 13 := rfl
  have hc41 : Nat.choose 54 41 = 1108176102180 := rfl
  have hs42 : 54 - 42 = 12 := rfl
  have hc42 : Nat.choose 54 42 = 343006888770 := rfl
  have hs43 : 54 - 43 = 11 := rfl
  have hc43 : Nat.choose 54 43 = 95722852680 := rfl
  have hs44 : 54 - 44 = 10 := rfl
  have hc44 : Nat.choose 54 44 = 23930713170 := rfl
  have hs45 : 54 - 45 = 9 := rfl
  have hc45 : Nat.choose 54 45 = 5317936260 := rfl
  have hs46 : 54 - 46 = 8 := rfl
  have hc46 : Nat.choose 54 46 = 1040465790 := rfl
  have hs47 : 54 - 47 = 7 := rfl
  have hc47 : Nat.choose 54 47 = 177100560 := rfl
  have hs48 : 54 - 48 = 6 := rfl
  have hc48 : Nat.choose 54 48 = 25827165 := rfl
  have hs49 : 54 - 49 = 5 := rfl
  have hc49 : Nat.choose 54 49 = 3162510 := rfl
  have hs50 : 54 - 50 = 4 := rfl
  have hc50 : Nat.choose 54 50 = 316251 := rfl
  have hs51 : 54 - 51 = 3 := rfl
  have hc51 : Nat.choose 54 51 = 24804 := rfl
  have hs52 : 54 - 52 = 2 := rfl
  have hc52 : Nat.choose 54 52 = 1431 := rfl
  have hs53 : 54 - 53 = 1 := rfl
  have hc53 : Nat.choose 54 53 = 54 := rfl
  have hs54 : 54 - 54 = 0 := rfl
  have hc54 : Nat.choose 54 54 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_54 : A195441 (55 - 1) = 798 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 55 - 0 = 55 := rfl
  have hc0 : Nat.choose 55 0 = 1 := rfl
  have hs1 : 55 - 1 = 54 := rfl
  have hc1 : Nat.choose 55 1 = 55 := rfl
  have hs2 : 55 - 2 = 53 := rfl
  have hc2 : Nat.choose 55 2 = 1485 := rfl
  have hs3 : 55 - 3 = 52 := rfl
  have hc3 : Nat.choose 55 3 = 26235 := rfl
  have hs4 : 55 - 4 = 51 := rfl
  have hc4 : Nat.choose 55 4 = 341055 := rfl
  have hs5 : 55 - 5 = 50 := rfl
  have hc5 : Nat.choose 55 5 = 3478761 := rfl
  have hs6 : 55 - 6 = 49 := rfl
  have hc6 : Nat.choose 55 6 = 28989675 := rfl
  have hs7 : 55 - 7 = 48 := rfl
  have hc7 : Nat.choose 55 7 = 202927725 := rfl
  have hs8 : 55 - 8 = 47 := rfl
  have hc8 : Nat.choose 55 8 = 1217566350 := rfl
  have hs9 : 55 - 9 = 46 := rfl
  have hc9 : Nat.choose 55 9 = 6358402050 := rfl
  have hs10 : 55 - 10 = 45 := rfl
  have hc10 : Nat.choose 55 10 = 29248649430 := rfl
  have hs11 : 55 - 11 = 44 := rfl
  have hc11 : Nat.choose 55 11 = 119653565850 := rfl
  have hs12 : 55 - 12 = 43 := rfl
  have hc12 : Nat.choose 55 12 = 438729741450 := rfl
  have hs13 : 55 - 13 = 42 := rfl
  have hc13 : Nat.choose 55 13 = 1451182990950 := rfl
  have hs14 : 55 - 14 = 41 := rfl
  have hc14 : Nat.choose 55 14 = 4353548972850 := rfl
  have hs15 : 55 - 15 = 40 := rfl
  have hc15 : Nat.choose 55 15 = 11899700525790 := rfl
  have hs16 : 55 - 16 = 39 := rfl
  have hc16 : Nat.choose 55 16 = 29749251314475 := rfl
  have hs17 : 55 - 17 = 38 := rfl
  have hc17 : Nat.choose 55 17 = 68248282427325 := rfl
  have hs18 : 55 - 18 = 37 := rfl
  have hc18 : Nat.choose 55 18 = 144079707346575 := rfl
  have hs19 : 55 - 19 = 36 := rfl
  have hc19 : Nat.choose 55 19 = 280576272201225 := rfl
  have hs20 : 55 - 20 = 35 := rfl
  have hc20 : Nat.choose 55 20 = 505037289962205 := rfl
  have hs21 : 55 - 21 = 34 := rfl
  have hc21 : Nat.choose 55 21 = 841728816603675 := rfl
  have hs22 : 55 - 22 = 33 := rfl
  have hc22 : Nat.choose 55 22 = 1300853625660225 := rfl
  have hs23 : 55 - 23 = 32 := rfl
  have hc23 : Nat.choose 55 23 = 1866442158555975 := rfl
  have hs24 : 55 - 24 = 31 := rfl
  have hc24 : Nat.choose 55 24 = 2488589544741300 := rfl
  have hs25 : 55 - 25 = 30 := rfl
  have hc25 : Nat.choose 55 25 = 3085851035479212 := rfl
  have hs26 : 55 - 26 = 29 := rfl
  have hc26 : Nat.choose 55 26 = 3560597348629860 := rfl
  have hs27 : 55 - 27 = 28 := rfl
  have hc27 : Nat.choose 55 27 = 3824345300380220 := rfl
  have hs28 : 55 - 28 = 27 := rfl
  have hc28 : Nat.choose 55 28 = 3824345300380220 := rfl
  have hs29 : 55 - 29 = 26 := rfl
  have hc29 : Nat.choose 55 29 = 3560597348629860 := rfl
  have hs30 : 55 - 30 = 25 := rfl
  have hc30 : Nat.choose 55 30 = 3085851035479212 := rfl
  have hs31 : 55 - 31 = 24 := rfl
  have hc31 : Nat.choose 55 31 = 2488589544741300 := rfl
  have hs32 : 55 - 32 = 23 := rfl
  have hc32 : Nat.choose 55 32 = 1866442158555975 := rfl
  have hs33 : 55 - 33 = 22 := rfl
  have hc33 : Nat.choose 55 33 = 1300853625660225 := rfl
  have hs34 : 55 - 34 = 21 := rfl
  have hc34 : Nat.choose 55 34 = 841728816603675 := rfl
  have hs35 : 55 - 35 = 20 := rfl
  have hc35 : Nat.choose 55 35 = 505037289962205 := rfl
  have hs36 : 55 - 36 = 19 := rfl
  have hc36 : Nat.choose 55 36 = 280576272201225 := rfl
  have hs37 : 55 - 37 = 18 := rfl
  have hc37 : Nat.choose 55 37 = 144079707346575 := rfl
  have hs38 : 55 - 38 = 17 := rfl
  have hc38 : Nat.choose 55 38 = 68248282427325 := rfl
  have hs39 : 55 - 39 = 16 := rfl
  have hc39 : Nat.choose 55 39 = 29749251314475 := rfl
  have hs40 : 55 - 40 = 15 := rfl
  have hc40 : Nat.choose 55 40 = 11899700525790 := rfl
  have hs41 : 55 - 41 = 14 := rfl
  have hc41 : Nat.choose 55 41 = 4353548972850 := rfl
  have hs42 : 55 - 42 = 13 := rfl
  have hc42 : Nat.choose 55 42 = 1451182990950 := rfl
  have hs43 : 55 - 43 = 12 := rfl
  have hc43 : Nat.choose 55 43 = 438729741450 := rfl
  have hs44 : 55 - 44 = 11 := rfl
  have hc44 : Nat.choose 55 44 = 119653565850 := rfl
  have hs45 : 55 - 45 = 10 := rfl
  have hc45 : Nat.choose 55 45 = 29248649430 := rfl
  have hs46 : 55 - 46 = 9 := rfl
  have hc46 : Nat.choose 55 46 = 6358402050 := rfl
  have hs47 : 55 - 47 = 8 := rfl
  have hc47 : Nat.choose 55 47 = 1217566350 := rfl
  have hs48 : 55 - 48 = 7 := rfl
  have hc48 : Nat.choose 55 48 = 202927725 := rfl
  have hs49 : 55 - 49 = 6 := rfl
  have hc49 : Nat.choose 55 49 = 28989675 := rfl
  have hs50 : 55 - 50 = 5 := rfl
  have hc50 : Nat.choose 55 50 = 3478761 := rfl
  have hs51 : 55 - 51 = 4 := rfl
  have hc51 : Nat.choose 55 51 = 341055 := rfl
  have hs52 : 55 - 52 = 3 := rfl
  have hc52 : Nat.choose 55 52 = 26235 := rfl
  have hs53 : 55 - 53 = 2 := rfl
  have hc53 : Nat.choose 55 53 = 1485 := rfl
  have hs54 : 55 - 54 = 1 := rfl
  have hc54 : Nat.choose 55 54 = 55 := rfl
  have hs55 : 55 - 55 = 0 := rfl
  have hc55 : Nat.choose 55 55 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54, hs55, hc55]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_54, bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_55 : A195441 (56 - 1) = 114 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 56 - 0 = 56 := rfl
  have hc0 : Nat.choose 56 0 = 1 := rfl
  have hs1 : 56 - 1 = 55 := rfl
  have hc1 : Nat.choose 56 1 = 56 := rfl
  have hs2 : 56 - 2 = 54 := rfl
  have hc2 : Nat.choose 56 2 = 1540 := rfl
  have hs3 : 56 - 3 = 53 := rfl
  have hc3 : Nat.choose 56 3 = 27720 := rfl
  have hs4 : 56 - 4 = 52 := rfl
  have hc4 : Nat.choose 56 4 = 367290 := rfl
  have hs5 : 56 - 5 = 51 := rfl
  have hc5 : Nat.choose 56 5 = 3819816 := rfl
  have hs6 : 56 - 6 = 50 := rfl
  have hc6 : Nat.choose 56 6 = 32468436 := rfl
  have hs7 : 56 - 7 = 49 := rfl
  have hc7 : Nat.choose 56 7 = 231917400 := rfl
  have hs8 : 56 - 8 = 48 := rfl
  have hc8 : Nat.choose 56 8 = 1420494075 := rfl
  have hs9 : 56 - 9 = 47 := rfl
  have hc9 : Nat.choose 56 9 = 7575968400 := rfl
  have hs10 : 56 - 10 = 46 := rfl
  have hc10 : Nat.choose 56 10 = 35607051480 := rfl
  have hs11 : 56 - 11 = 45 := rfl
  have hc11 : Nat.choose 56 11 = 148902215280 := rfl
  have hs12 : 56 - 12 = 44 := rfl
  have hc12 : Nat.choose 56 12 = 558383307300 := rfl
  have hs13 : 56 - 13 = 43 := rfl
  have hc13 : Nat.choose 56 13 = 1889912732400 := rfl
  have hs14 : 56 - 14 = 42 := rfl
  have hc14 : Nat.choose 56 14 = 5804731963800 := rfl
  have hs15 : 56 - 15 = 41 := rfl
  have hc15 : Nat.choose 56 15 = 16253249498640 := rfl
  have hs16 : 56 - 16 = 40 := rfl
  have hc16 : Nat.choose 56 16 = 41648951840265 := rfl
  have hs17 : 56 - 17 = 39 := rfl
  have hc17 : Nat.choose 56 17 = 97997533741800 := rfl
  have hs18 : 56 - 18 = 38 := rfl
  have hc18 : Nat.choose 56 18 = 212327989773900 := rfl
  have hs19 : 56 - 19 = 37 := rfl
  have hc19 : Nat.choose 56 19 = 424655979547800 := rfl
  have hs20 : 56 - 20 = 36 := rfl
  have hc20 : Nat.choose 56 20 = 785613562163430 := rfl
  have hs21 : 56 - 21 = 35 := rfl
  have hc21 : Nat.choose 56 21 = 1346766106565880 := rfl
  have hs22 : 56 - 22 = 34 := rfl
  have hc22 : Nat.choose 56 22 = 2142582442263900 := rfl
  have hs23 : 56 - 23 = 33 := rfl
  have hc23 : Nat.choose 56 23 = 3167295784216200 := rfl
  have hs24 : 56 - 24 = 32 := rfl
  have hc24 : Nat.choose 56 24 = 4355031703297275 := rfl
  have hs25 : 56 - 25 = 31 := rfl
  have hc25 : Nat.choose 56 25 = 5574440580220512 := rfl
  have hs26 : 56 - 26 = 30 := rfl
  have hc26 : Nat.choose 56 26 = 6646448384109072 := rfl
  have hs27 : 56 - 27 = 29 := rfl
  have hc27 : Nat.choose 56 27 = 7384942649010080 := rfl
  have hs28 : 56 - 28 = 28 := rfl
  have hc28 : Nat.choose 56 28 = 7648690600760440 := rfl
  have hs29 : 56 - 29 = 27 := rfl
  have hc29 : Nat.choose 56 29 = 7384942649010080 := rfl
  have hs30 : 56 - 30 = 26 := rfl
  have hc30 : Nat.choose 56 30 = 6646448384109072 := rfl
  have hs31 : 56 - 31 = 25 := rfl
  have hc31 : Nat.choose 56 31 = 5574440580220512 := rfl
  have hs32 : 56 - 32 = 24 := rfl
  have hc32 : Nat.choose 56 32 = 4355031703297275 := rfl
  have hs33 : 56 - 33 = 23 := rfl
  have hc33 : Nat.choose 56 33 = 3167295784216200 := rfl
  have hs34 : 56 - 34 = 22 := rfl
  have hc34 : Nat.choose 56 34 = 2142582442263900 := rfl
  have hs35 : 56 - 35 = 21 := rfl
  have hc35 : Nat.choose 56 35 = 1346766106565880 := rfl
  have hs36 : 56 - 36 = 20 := rfl
  have hc36 : Nat.choose 56 36 = 785613562163430 := rfl
  have hs37 : 56 - 37 = 19 := rfl
  have hc37 : Nat.choose 56 37 = 424655979547800 := rfl
  have hs38 : 56 - 38 = 18 := rfl
  have hc38 : Nat.choose 56 38 = 212327989773900 := rfl
  have hs39 : 56 - 39 = 17 := rfl
  have hc39 : Nat.choose 56 39 = 97997533741800 := rfl
  have hs40 : 56 - 40 = 16 := rfl
  have hc40 : Nat.choose 56 40 = 41648951840265 := rfl
  have hs41 : 56 - 41 = 15 := rfl
  have hc41 : Nat.choose 56 41 = 16253249498640 := rfl
  have hs42 : 56 - 42 = 14 := rfl
  have hc42 : Nat.choose 56 42 = 5804731963800 := rfl
  have hs43 : 56 - 43 = 13 := rfl
  have hc43 : Nat.choose 56 43 = 1889912732400 := rfl
  have hs44 : 56 - 44 = 12 := rfl
  have hc44 : Nat.choose 56 44 = 558383307300 := rfl
  have hs45 : 56 - 45 = 11 := rfl
  have hc45 : Nat.choose 56 45 = 148902215280 := rfl
  have hs46 : 56 - 46 = 10 := rfl
  have hc46 : Nat.choose 56 46 = 35607051480 := rfl
  have hs47 : 56 - 47 = 9 := rfl
  have hc47 : Nat.choose 56 47 = 7575968400 := rfl
  have hs48 : 56 - 48 = 8 := rfl
  have hc48 : Nat.choose 56 48 = 1420494075 := rfl
  have hs49 : 56 - 49 = 7 := rfl
  have hc49 : Nat.choose 56 49 = 231917400 := rfl
  have hs50 : 56 - 50 = 6 := rfl
  have hc50 : Nat.choose 56 50 = 32468436 := rfl
  have hs51 : 56 - 51 = 5 := rfl
  have hc51 : Nat.choose 56 51 = 3819816 := rfl
  have hs52 : 56 - 52 = 4 := rfl
  have hc52 : Nat.choose 56 52 = 367290 := rfl
  have hs53 : 56 - 53 = 3 := rfl
  have hc53 : Nat.choose 56 53 = 27720 := rfl
  have hs54 : 56 - 54 = 2 := rfl
  have hc54 : Nat.choose 56 54 = 1540 := rfl
  have hs55 : 56 - 55 = 1 := rfl
  have hc55 : Nat.choose 56 55 = 56 := rfl
  have hs56 : 56 - 56 = 0 := rfl
  have hc56 : Nat.choose 56 56 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54, hs55, hc55, hs56, hc56]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_54, bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_56 : A195441 (57 - 1) = 870 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 57 - 0 = 57 := rfl
  have hc0 : Nat.choose 57 0 = 1 := rfl
  have hs1 : 57 - 1 = 56 := rfl
  have hc1 : Nat.choose 57 1 = 57 := rfl
  have hs2 : 57 - 2 = 55 := rfl
  have hc2 : Nat.choose 57 2 = 1596 := rfl
  have hs3 : 57 - 3 = 54 := rfl
  have hc3 : Nat.choose 57 3 = 29260 := rfl
  have hs4 : 57 - 4 = 53 := rfl
  have hc4 : Nat.choose 57 4 = 395010 := rfl
  have hs5 : 57 - 5 = 52 := rfl
  have hc5 : Nat.choose 57 5 = 4187106 := rfl
  have hs6 : 57 - 6 = 51 := rfl
  have hc6 : Nat.choose 57 6 = 36288252 := rfl
  have hs7 : 57 - 7 = 50 := rfl
  have hc7 : Nat.choose 57 7 = 264385836 := rfl
  have hs8 : 57 - 8 = 49 := rfl
  have hc8 : Nat.choose 57 8 = 1652411475 := rfl
  have hs9 : 57 - 9 = 48 := rfl
  have hc9 : Nat.choose 57 9 = 8996462475 := rfl
  have hs10 : 57 - 10 = 47 := rfl
  have hc10 : Nat.choose 57 10 = 43183019880 := rfl
  have hs11 : 57 - 11 = 46 := rfl
  have hc11 : Nat.choose 57 11 = 184509266760 := rfl
  have hs12 : 57 - 12 = 45 := rfl
  have hc12 : Nat.choose 57 12 = 707285522580 := rfl
  have hs13 : 57 - 13 = 44 := rfl
  have hc13 : Nat.choose 57 13 = 2448296039700 := rfl
  have hs14 : 57 - 14 = 43 := rfl
  have hc14 : Nat.choose 57 14 = 7694644696200 := rfl
  have hs15 : 57 - 15 = 42 := rfl
  have hc15 : Nat.choose 57 15 = 22057981462440 := rfl
  have hs16 : 57 - 16 = 41 := rfl
  have hc16 : Nat.choose 57 16 = 57902201338905 := rfl
  have hs17 : 57 - 17 = 40 := rfl
  have hc17 : Nat.choose 57 17 = 139646485582065 := rfl
  have hs18 : 57 - 18 = 39 := rfl
  have hc18 : Nat.choose 57 18 = 310325523515700 := rfl
  have hs19 : 57 - 19 = 38 := rfl
  have hc19 : Nat.choose 57 19 = 636983969321700 := rfl
  have hs20 : 57 - 20 = 37 := rfl
  have hc20 : Nat.choose 57 20 = 1210269541711230 := rfl
  have hs21 : 57 - 21 = 36 := rfl
  have hc21 : Nat.choose 57 21 = 2132379668729310 := rfl
  have hs22 : 57 - 22 = 35 := rfl
  have hc22 : Nat.choose 57 22 = 3489348548829780 := rfl
  have hs23 : 57 - 23 = 34 := rfl
  have hc23 : Nat.choose 57 23 = 5309878226480100 := rfl
  have hs24 : 57 - 24 = 33 := rfl
  have hc24 : Nat.choose 57 24 = 7522327487513475 := rfl
  have hs25 : 57 - 25 = 32 := rfl
  have hc25 : Nat.choose 57 25 = 9929472283517787 := rfl
  have hs26 : 57 - 26 = 31 := rfl
  have hc26 : Nat.choose 57 26 = 12220888964329584 := rfl
  have hs27 : 57 - 27 = 30 := rfl
  have hc27 : Nat.choose 57 27 = 14031391033119152 := rfl
  have hs28 : 57 - 28 = 29 := rfl
  have hc28 : Nat.choose 57 28 = 15033633249770520 := rfl
  have hs29 : 57 - 29 = 28 := rfl
  have hc29 : Nat.choose 57 29 = 15033633249770520 := rfl
  have hs30 : 57 - 30 = 27 := rfl
  have hc30 : Nat.choose 57 30 = 14031391033119152 := rfl
  have hs31 : 57 - 31 = 26 := rfl
  have hc31 : Nat.choose 57 31 = 12220888964329584 := rfl
  have hs32 : 57 - 32 = 25 := rfl
  have hc32 : Nat.choose 57 32 = 9929472283517787 := rfl
  have hs33 : 57 - 33 = 24 := rfl
  have hc33 : Nat.choose 57 33 = 7522327487513475 := rfl
  have hs34 : 57 - 34 = 23 := rfl
  have hc34 : Nat.choose 57 34 = 5309878226480100 := rfl
  have hs35 : 57 - 35 = 22 := rfl
  have hc35 : Nat.choose 57 35 = 3489348548829780 := rfl
  have hs36 : 57 - 36 = 21 := rfl
  have hc36 : Nat.choose 57 36 = 2132379668729310 := rfl
  have hs37 : 57 - 37 = 20 := rfl
  have hc37 : Nat.choose 57 37 = 1210269541711230 := rfl
  have hs38 : 57 - 38 = 19 := rfl
  have hc38 : Nat.choose 57 38 = 636983969321700 := rfl
  have hs39 : 57 - 39 = 18 := rfl
  have hc39 : Nat.choose 57 39 = 310325523515700 := rfl
  have hs40 : 57 - 40 = 17 := rfl
  have hc40 : Nat.choose 57 40 = 139646485582065 := rfl
  have hs41 : 57 - 41 = 16 := rfl
  have hc41 : Nat.choose 57 41 = 57902201338905 := rfl
  have hs42 : 57 - 42 = 15 := rfl
  have hc42 : Nat.choose 57 42 = 22057981462440 := rfl
  have hs43 : 57 - 43 = 14 := rfl
  have hc43 : Nat.choose 57 43 = 7694644696200 := rfl
  have hs44 : 57 - 44 = 13 := rfl
  have hc44 : Nat.choose 57 44 = 2448296039700 := rfl
  have hs45 : 57 - 45 = 12 := rfl
  have hc45 : Nat.choose 57 45 = 707285522580 := rfl
  have hs46 : 57 - 46 = 11 := rfl
  have hc46 : Nat.choose 57 46 = 184509266760 := rfl
  have hs47 : 57 - 47 = 10 := rfl
  have hc47 : Nat.choose 57 47 = 43183019880 := rfl
  have hs48 : 57 - 48 = 9 := rfl
  have hc48 : Nat.choose 57 48 = 8996462475 := rfl
  have hs49 : 57 - 49 = 8 := rfl
  have hc49 : Nat.choose 57 49 = 1652411475 := rfl
  have hs50 : 57 - 50 = 7 := rfl
  have hc50 : Nat.choose 57 50 = 264385836 := rfl
  have hs51 : 57 - 51 = 6 := rfl
  have hc51 : Nat.choose 57 51 = 36288252 := rfl
  have hs52 : 57 - 52 = 5 := rfl
  have hc52 : Nat.choose 57 52 = 4187106 := rfl
  have hs53 : 57 - 53 = 4 := rfl
  have hc53 : Nat.choose 57 53 = 395010 := rfl
  have hs54 : 57 - 54 = 3 := rfl
  have hc54 : Nat.choose 57 54 = 29260 := rfl
  have hs55 : 57 - 55 = 2 := rfl
  have hc55 : Nat.choose 57 55 = 1596 := rfl
  have hs56 : 57 - 56 = 1 := rfl
  have hc56 : Nat.choose 57 56 = 57 := rfl
  have hs57 : 57 - 57 = 0 := rfl
  have hc57 : Nat.choose 57 57 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54, hs55, hc55, hs56, hc56, hs57, hc57]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_56, bernoulli_val_54, bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_57 : A195441 (58 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 58 - 0 = 58 := rfl
  have hc0 : Nat.choose 58 0 = 1 := rfl
  have hs1 : 58 - 1 = 57 := rfl
  have hc1 : Nat.choose 58 1 = 58 := rfl
  have hs2 : 58 - 2 = 56 := rfl
  have hc2 : Nat.choose 58 2 = 1653 := rfl
  have hs3 : 58 - 3 = 55 := rfl
  have hc3 : Nat.choose 58 3 = 30856 := rfl
  have hs4 : 58 - 4 = 54 := rfl
  have hc4 : Nat.choose 58 4 = 424270 := rfl
  have hs5 : 58 - 5 = 53 := rfl
  have hc5 : Nat.choose 58 5 = 4582116 := rfl
  have hs6 : 58 - 6 = 52 := rfl
  have hc6 : Nat.choose 58 6 = 40475358 := rfl
  have hs7 : 58 - 7 = 51 := rfl
  have hc7 : Nat.choose 58 7 = 300674088 := rfl
  have hs8 : 58 - 8 = 50 := rfl
  have hc8 : Nat.choose 58 8 = 1916797311 := rfl
  have hs9 : 58 - 9 = 49 := rfl
  have hc9 : Nat.choose 58 9 = 10648873950 := rfl
  have hs10 : 58 - 10 = 48 := rfl
  have hc10 : Nat.choose 58 10 = 52179482355 := rfl
  have hs11 : 58 - 11 = 47 := rfl
  have hc11 : Nat.choose 58 11 = 227692286640 := rfl
  have hs12 : 58 - 12 = 46 := rfl
  have hc12 : Nat.choose 58 12 = 891794789340 := rfl
  have hs13 : 58 - 13 = 45 := rfl
  have hc13 : Nat.choose 58 13 = 3155581562280 := rfl
  have hs14 : 58 - 14 = 44 := rfl
  have hc14 : Nat.choose 58 14 = 10142940735900 := rfl
  have hs15 : 58 - 15 = 43 := rfl
  have hc15 : Nat.choose 58 15 = 29752626158640 := rfl
  have hs16 : 58 - 16 = 42 := rfl
  have hc16 : Nat.choose 58 16 = 79960182801345 := rfl
  have hs17 : 58 - 17 = 41 := rfl
  have hc17 : Nat.choose 58 17 = 197548686920970 := rfl
  have hs18 : 58 - 18 = 40 := rfl
  have hc18 : Nat.choose 58 18 = 449972009097765 := rfl
  have hs19 : 58 - 19 = 39 := rfl
  have hc19 : Nat.choose 58 19 = 947309492837400 := rfl
  have hs20 : 58 - 20 = 38 := rfl
  have hc20 : Nat.choose 58 20 = 1847253511032930 := rfl
  have hs21 : 58 - 21 = 37 := rfl
  have hc21 : Nat.choose 58 21 = 3342649210440540 := rfl
  have hs22 : 58 - 22 = 36 := rfl
  have hc22 : Nat.choose 58 22 = 5621728217559090 := rfl
  have hs23 : 58 - 23 = 35 := rfl
  have hc23 : Nat.choose 58 23 = 8799226775309880 := rfl
  have hs24 : 58 - 24 = 34 := rfl
  have hc24 : Nat.choose 58 24 = 12832205713993575 := rfl
  have hs25 : 58 - 25 = 33 := rfl
  have hc25 : Nat.choose 58 25 = 17451799771031262 := rfl
  have hs26 : 58 - 26 = 32 := rfl
  have hc26 : Nat.choose 58 26 = 22150361247847371 := rfl
  have hs27 : 58 - 27 = 31 := rfl
  have hc27 : Nat.choose 58 27 = 26252279997448736 := rfl
  have hs28 : 58 - 28 = 30 := rfl
  have hc28 : Nat.choose 58 28 = 29065024282889672 := rfl
  have hs29 : 58 - 29 = 29 := rfl
  have hc29 : Nat.choose 58 29 = 30067266499541040 := rfl
  have hs30 : 58 - 30 = 28 := rfl
  have hc30 : Nat.choose 58 30 = 29065024282889672 := rfl
  have hs31 : 58 - 31 = 27 := rfl
  have hc31 : Nat.choose 58 31 = 26252279997448736 := rfl
  have hs32 : 58 - 32 = 26 := rfl
  have hc32 : Nat.choose 58 32 = 22150361247847371 := rfl
  have hs33 : 58 - 33 = 25 := rfl
  have hc33 : Nat.choose 58 33 = 17451799771031262 := rfl
  have hs34 : 58 - 34 = 24 := rfl
  have hc34 : Nat.choose 58 34 = 12832205713993575 := rfl
  have hs35 : 58 - 35 = 23 := rfl
  have hc35 : Nat.choose 58 35 = 8799226775309880 := rfl
  have hs36 : 58 - 36 = 22 := rfl
  have hc36 : Nat.choose 58 36 = 5621728217559090 := rfl
  have hs37 : 58 - 37 = 21 := rfl
  have hc37 : Nat.choose 58 37 = 3342649210440540 := rfl
  have hs38 : 58 - 38 = 20 := rfl
  have hc38 : Nat.choose 58 38 = 1847253511032930 := rfl
  have hs39 : 58 - 39 = 19 := rfl
  have hc39 : Nat.choose 58 39 = 947309492837400 := rfl
  have hs40 : 58 - 40 = 18 := rfl
  have hc40 : Nat.choose 58 40 = 449972009097765 := rfl
  have hs41 : 58 - 41 = 17 := rfl
  have hc41 : Nat.choose 58 41 = 197548686920970 := rfl
  have hs42 : 58 - 42 = 16 := rfl
  have hc42 : Nat.choose 58 42 = 79960182801345 := rfl
  have hs43 : 58 - 43 = 15 := rfl
  have hc43 : Nat.choose 58 43 = 29752626158640 := rfl
  have hs44 : 58 - 44 = 14 := rfl
  have hc44 : Nat.choose 58 44 = 10142940735900 := rfl
  have hs45 : 58 - 45 = 13 := rfl
  have hc45 : Nat.choose 58 45 = 3155581562280 := rfl
  have hs46 : 58 - 46 = 12 := rfl
  have hc46 : Nat.choose 58 46 = 891794789340 := rfl
  have hs47 : 58 - 47 = 11 := rfl
  have hc47 : Nat.choose 58 47 = 227692286640 := rfl
  have hs48 : 58 - 48 = 10 := rfl
  have hc48 : Nat.choose 58 48 = 52179482355 := rfl
  have hs49 : 58 - 49 = 9 := rfl
  have hc49 : Nat.choose 58 49 = 10648873950 := rfl
  have hs50 : 58 - 50 = 8 := rfl
  have hc50 : Nat.choose 58 50 = 1916797311 := rfl
  have hs51 : 58 - 51 = 7 := rfl
  have hc51 : Nat.choose 58 51 = 300674088 := rfl
  have hs52 : 58 - 52 = 6 := rfl
  have hc52 : Nat.choose 58 52 = 40475358 := rfl
  have hs53 : 58 - 53 = 5 := rfl
  have hc53 : Nat.choose 58 53 = 4582116 := rfl
  have hs54 : 58 - 54 = 4 := rfl
  have hc54 : Nat.choose 58 54 = 424270 := rfl
  have hs55 : 58 - 55 = 3 := rfl
  have hc55 : Nat.choose 58 55 = 30856 := rfl
  have hs56 : 58 - 56 = 2 := rfl
  have hc56 : Nat.choose 58 56 = 1653 := rfl
  have hs57 : 58 - 57 = 1 := rfl
  have hc57 : Nat.choose 58 57 = 58 := rfl
  have hs58 : 58 - 58 = 0 := rfl
  have hc58 : Nat.choose 58 58 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54, hs55, hc55, hs56, hc56, hs57, hc57, hs58, hc58]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_56, bernoulli_val_54, bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num

theorem A195441_val_58 : A195441 (59 - 1) = 30 := by
  unfold A195441
  simp only [range_add_one, lcm_insert, range_zero, lcm_empty]
  simp only [coeff_bernoulli_sub_C_bernoulli]
  have hs0 : 59 - 0 = 59 := rfl
  have hc0 : Nat.choose 59 0 = 1 := rfl
  have hs1 : 59 - 1 = 58 := rfl
  have hc1 : Nat.choose 59 1 = 59 := rfl
  have hs2 : 59 - 2 = 57 := rfl
  have hc2 : Nat.choose 59 2 = 1711 := rfl
  have hs3 : 59 - 3 = 56 := rfl
  have hc3 : Nat.choose 59 3 = 32509 := rfl
  have hs4 : 59 - 4 = 55 := rfl
  have hc4 : Nat.choose 59 4 = 455126 := rfl
  have hs5 : 59 - 5 = 54 := rfl
  have hc5 : Nat.choose 59 5 = 5006386 := rfl
  have hs6 : 59 - 6 = 53 := rfl
  have hc6 : Nat.choose 59 6 = 45057474 := rfl
  have hs7 : 59 - 7 = 52 := rfl
  have hc7 : Nat.choose 59 7 = 341149446 := rfl
  have hs8 : 59 - 8 = 51 := rfl
  have hc8 : Nat.choose 59 8 = 2217471399 := rfl
  have hs9 : 59 - 9 = 50 := rfl
  have hc9 : Nat.choose 59 9 = 12565671261 := rfl
  have hs10 : 59 - 10 = 49 := rfl
  have hc10 : Nat.choose 59 10 = 62828356305 := rfl
  have hs11 : 59 - 11 = 48 := rfl
  have hc11 : Nat.choose 59 11 = 279871768995 := rfl
  have hs12 : 59 - 12 = 47 := rfl
  have hc12 : Nat.choose 59 12 = 1119487075980 := rfl
  have hs13 : 59 - 13 = 46 := rfl
  have hc13 : Nat.choose 59 13 = 4047376351620 := rfl
  have hs14 : 59 - 14 = 45 := rfl
  have hc14 : Nat.choose 59 14 = 13298522298180 := rfl
  have hs15 : 59 - 15 = 44 := rfl
  have hc15 : Nat.choose 59 15 = 39895566894540 := rfl
  have hs16 : 59 - 16 = 43 := rfl
  have hc16 : Nat.choose 59 16 = 109712808959985 := rfl
  have hs17 : 59 - 17 = 42 := rfl
  have hc17 : Nat.choose 59 17 = 277508869722315 := rfl
  have hs18 : 59 - 18 = 41 := rfl
  have hc18 : Nat.choose 59 18 = 647520696018735 := rfl
  have hs19 : 59 - 19 = 40 := rfl
  have hc19 : Nat.choose 59 19 = 1397281501935165 := rfl
  have hs20 : 59 - 20 = 39 := rfl
  have hc20 : Nat.choose 59 20 = 2794563003870330 := rfl
  have hs21 : 59 - 21 = 38 := rfl
  have hc21 : Nat.choose 59 21 = 5189902721473470 := rfl
  have hs22 : 59 - 22 = 37 := rfl
  have hc22 : Nat.choose 59 22 = 8964377427999630 := rfl
  have hs23 : 59 - 23 = 36 := rfl
  have hc23 : Nat.choose 59 23 = 14420954992868970 := rfl
  have hs24 : 59 - 24 = 35 := rfl
  have hc24 : Nat.choose 59 24 = 21631432489303455 := rfl
  have hs25 : 59 - 25 = 34 := rfl
  have hc25 : Nat.choose 59 25 = 30284005485024837 := rfl
  have hs26 : 59 - 26 = 33 := rfl
  have hc26 : Nat.choose 59 26 = 39602161018878633 := rfl
  have hs27 : 59 - 27 = 32 := rfl
  have hc27 : Nat.choose 59 27 = 48402641245296107 := rfl
  have hs28 : 59 - 28 = 31 := rfl
  have hc28 : Nat.choose 59 28 = 55317304280338408 := rfl
  have hs29 : 59 - 29 = 30 := rfl
  have hc29 : Nat.choose 59 29 = 59132290782430712 := rfl
  have hs30 : 59 - 30 = 29 := rfl
  have hc30 : Nat.choose 59 30 = 59132290782430712 := rfl
  have hs31 : 59 - 31 = 28 := rfl
  have hc31 : Nat.choose 59 31 = 55317304280338408 := rfl
  have hs32 : 59 - 32 = 27 := rfl
  have hc32 : Nat.choose 59 32 = 48402641245296107 := rfl
  have hs33 : 59 - 33 = 26 := rfl
  have hc33 : Nat.choose 59 33 = 39602161018878633 := rfl
  have hs34 : 59 - 34 = 25 := rfl
  have hc34 : Nat.choose 59 34 = 30284005485024837 := rfl
  have hs35 : 59 - 35 = 24 := rfl
  have hc35 : Nat.choose 59 35 = 21631432489303455 := rfl
  have hs36 : 59 - 36 = 23 := rfl
  have hc36 : Nat.choose 59 36 = 14420954992868970 := rfl
  have hs37 : 59 - 37 = 22 := rfl
  have hc37 : Nat.choose 59 37 = 8964377427999630 := rfl
  have hs38 : 59 - 38 = 21 := rfl
  have hc38 : Nat.choose 59 38 = 5189902721473470 := rfl
  have hs39 : 59 - 39 = 20 := rfl
  have hc39 : Nat.choose 59 39 = 2794563003870330 := rfl
  have hs40 : 59 - 40 = 19 := rfl
  have hc40 : Nat.choose 59 40 = 1397281501935165 := rfl
  have hs41 : 59 - 41 = 18 := rfl
  have hc41 : Nat.choose 59 41 = 647520696018735 := rfl
  have hs42 : 59 - 42 = 17 := rfl
  have hc42 : Nat.choose 59 42 = 277508869722315 := rfl
  have hs43 : 59 - 43 = 16 := rfl
  have hc43 : Nat.choose 59 43 = 109712808959985 := rfl
  have hs44 : 59 - 44 = 15 := rfl
  have hc44 : Nat.choose 59 44 = 39895566894540 := rfl
  have hs45 : 59 - 45 = 14 := rfl
  have hc45 : Nat.choose 59 45 = 13298522298180 := rfl
  have hs46 : 59 - 46 = 13 := rfl
  have hc46 : Nat.choose 59 46 = 4047376351620 := rfl
  have hs47 : 59 - 47 = 12 := rfl
  have hc47 : Nat.choose 59 47 = 1119487075980 := rfl
  have hs48 : 59 - 48 = 11 := rfl
  have hc48 : Nat.choose 59 48 = 279871768995 := rfl
  have hs49 : 59 - 49 = 10 := rfl
  have hc49 : Nat.choose 59 49 = 62828356305 := rfl
  have hs50 : 59 - 50 = 9 := rfl
  have hc50 : Nat.choose 59 50 = 12565671261 := rfl
  have hs51 : 59 - 51 = 8 := rfl
  have hc51 : Nat.choose 59 51 = 2217471399 := rfl
  have hs52 : 59 - 52 = 7 := rfl
  have hc52 : Nat.choose 59 52 = 341149446 := rfl
  have hs53 : 59 - 53 = 6 := rfl
  have hc53 : Nat.choose 59 53 = 45057474 := rfl
  have hs54 : 59 - 54 = 5 := rfl
  have hc54 : Nat.choose 59 54 = 5006386 := rfl
  have hs55 : 59 - 55 = 4 := rfl
  have hc55 : Nat.choose 59 55 = 455126 := rfl
  have hs56 : 59 - 56 = 3 := rfl
  have hc56 : Nat.choose 59 56 = 32509 := rfl
  have hs57 : 59 - 57 = 2 := rfl
  have hc57 : Nat.choose 59 57 = 1711 := rfl
  have hs58 : 59 - 58 = 1 := rfl
  have hc58 : Nat.choose 59 58 = 59 := rfl
  have hs59 : 59 - 59 = 0 := rfl
  have hc59 : Nat.choose 59 59 = 1 := rfl
  simp only [hs0, hc0, hs1, hc1, hs2, hc2, hs3, hc3, hs4, hc4, hs5, hc5, hs6, hc6, hs7, hc7, hs8, hc8, hs9, hc9, hs10, hc10, hs11, hc11, hs12, hc12, hs13, hc13, hs14, hc14, hs15, hc15, hs16, hc16, hs17, hc17, hs18, hc18, hs19, hc19, hs20, hc20, hs21, hc21, hs22, hc22, hs23, hc23, hs24, hc24, hs25, hc25, hs26, hc26, hs27, hc27, hs28, hc28, hs29, hc29, hs30, hc30, hs31, hc31, hs32, hc32, hs33, hc33, hs34, hc34, hs35, hc35, hs36, hc36, hs37, hc37, hs38, hc38, hs39, hc39, hs40, hc40, hs41, hc41, hs42, hc42, hs43, hc43, hs44, hc44, hs45, hc45, hs46, hc46, hs47, hc47, hs48, hc48, hs49, hc49, hs50, hc50, hs51, hc51, hs52, hc52, hs53, hc53, hs54, hc54, hs55, hc55, hs56, hc56, hs57, hc57, hs58, hc58, hs59, hc59]
  try simp only [bernoulli_eq_zero_of_odd, _root_.bernoulli_one, bernoulli_val_0]
  try simp only [bernoulli_val_58, bernoulli_val_56, bernoulli_val_54, bernoulli_val_52, bernoulli_val_50, bernoulli_val_48, bernoulli_val_46, bernoulli_val_44, bernoulli_val_42, bernoulli_val_40, bernoulli_val_38, bernoulli_val_36, bernoulli_val_34, bernoulli_val_32, bernoulli_val_30, bernoulli_val_28, bernoulli_val_26, bernoulli_val_24, bernoulli_val_22, bernoulli_val_20, bernoulli_val_18, bernoulli_val_16, bernoulli_val_14, bernoulli_val_12, bernoulli_val_10, bernoulli_val_8, bernoulli_val_6, bernoulli_val_4]
  try simp only [GCDMonoid_lcm_eq_Nat_lcm]
  norm_num


theorem oeis_a195441_conjecture_set_of_solutions :
    { n : ℕ | 1 ≤ n ∧ A195441 (n - 1) = radical (n + 1) } =
    ({3, 5, 8, 9, 11, 27, 29, 35, 59} : Finset ℕ).toSet := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with ⟨h1, h_eq⟩
    by_cases hnlt : n < 60
    · interval_cases n
      · rw [A195441_val_0, radical_2] at h_eq
        revert h_eq; decide
      · rw [A195441_val_1, radical_3] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_3, radical_5] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_5, radical_7] at h_eq
        revert h_eq; decide
      · rw [A195441_val_6, radical_8] at h_eq
        revert h_eq; decide
      · decide
      · decide
      · rw [A195441_val_9, radical_11] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_11, radical_13] at h_eq
        revert h_eq; decide
      · rw [A195441_val_12, radical_14] at h_eq
        revert h_eq; decide
      · rw [A195441_val_13, radical_15] at h_eq
        revert h_eq; decide
      · rw [A195441_val_14, radical_16] at h_eq
        revert h_eq; decide
      · rw [A195441_val_15, radical_17] at h_eq
        revert h_eq; decide
      · rw [A195441_val_16, radical_18] at h_eq
        revert h_eq; decide
      · rw [A195441_val_17, radical_19] at h_eq
        revert h_eq; decide
      · rw [A195441_val_18, radical_20] at h_eq
        revert h_eq; decide
      · rw [A195441_val_19, radical_21] at h_eq
        revert h_eq; decide
      · rw [A195441_val_20, radical_22] at h_eq
        revert h_eq; decide
      · rw [A195441_val_21, radical_23] at h_eq
        revert h_eq; decide
      · rw [A195441_val_22, radical_24] at h_eq
        revert h_eq; decide
      · rw [A195441_val_23, radical_25] at h_eq
        revert h_eq; decide
      · rw [A195441_val_24, radical_26] at h_eq
        revert h_eq; decide
      · rw [A195441_val_25, radical_27] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_27, radical_29] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_29, radical_31] at h_eq
        revert h_eq; decide
      · rw [A195441_val_30, radical_32] at h_eq
        revert h_eq; decide
      · rw [A195441_val_31, radical_33] at h_eq
        revert h_eq; decide
      · rw [A195441_val_32, radical_34] at h_eq
        revert h_eq; decide
      · rw [A195441_val_33, radical_35] at h_eq
        revert h_eq; decide
      · decide
      · rw [A195441_val_35, radical_37] at h_eq
        revert h_eq; decide
      · rw [A195441_val_36, radical_38] at h_eq
        revert h_eq; decide
      · rw [A195441_val_37, radical_39] at h_eq
        revert h_eq; decide
      · rw [A195441_val_38, radical_40] at h_eq
        revert h_eq; decide
      · rw [A195441_val_39, radical_41] at h_eq
        revert h_eq; decide
      · rw [A195441_val_40, radical_42] at h_eq
        revert h_eq; decide
      · rw [A195441_val_41, radical_43] at h_eq
        revert h_eq; decide
      · rw [A195441_val_42, radical_44] at h_eq
        revert h_eq; decide
      · rw [A195441_val_43, radical_45] at h_eq
        revert h_eq; decide
      · rw [A195441_val_44, radical_46] at h_eq
        revert h_eq; decide
      · rw [A195441_val_45, radical_47] at h_eq
        revert h_eq; decide
      · rw [A195441_val_46, radical_48] at h_eq
        revert h_eq; decide
      · rw [A195441_val_47, radical_49] at h_eq
        revert h_eq; decide
      · rw [A195441_val_48, radical_50] at h_eq
        revert h_eq; decide
      · rw [A195441_val_49, radical_51] at h_eq
        revert h_eq; decide
      · rw [A195441_val_50, radical_52] at h_eq
        revert h_eq; decide
      · rw [A195441_val_51, radical_53] at h_eq
        revert h_eq; decide
      · rw [A195441_val_52, radical_54] at h_eq
        revert h_eq; decide
      · rw [A195441_val_53, radical_55] at h_eq
        revert h_eq; decide
      · rw [A195441_val_54, radical_56] at h_eq
        revert h_eq; decide
      · rw [A195441_val_55, radical_57] at h_eq
        revert h_eq; decide
      · rw [A195441_val_56, radical_58] at h_eq
        revert h_eq; decide
      · rw [A195441_val_57, radical_59] at h_eq
        revert h_eq; decide
      · decide
    · sorry
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_2, radical_4]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_4, radical_6]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_7, radical_9]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_8, radical_10]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_10, radical_12]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_26, radical_28]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_28, radical_30]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_34, radical_36]
    · refine ⟨by decide, ?_⟩
      rw [A195441_val_58, radical_60]
