import Submission.PiVals

lemma bound_le_helper (m m0 : ℕ) (hm : m ≤ m0) : m * (m + 1) / 2 ≤ m0 * (m0 + 1) / 2 := by
  have : m * (m + 1) ≤ m0 * (m0 + 1) := by nlinarith
  omega

lemma bound_gt_helper (m m1 : ℕ) (hm : m1 ≤ m) : m1 * (m1 + 1) / 2 ≤ m * (m + 1) / 2 := by
  have : m1 * (m1 + 1) ≤ m * (m + 1) := by nlinarith
  omega



lemma no_sol_k_0 (m : ℕ) (hm1 : m ≥ 1) : my_pi (0*1) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 0*1 = 0 := by decide
  rw [hk_eq]
  have hk : my_pi (0) = 0 := pi_0
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_1 (m : ℕ) (hm1 : m ≥ 1) : my_pi (1*2) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 1*2 = 2 := by decide
  rw [hk_eq]
  have hk : my_pi (2) = 1 := pi_2
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_2 (m : ℕ) (hm1 : m ≥ 1) : my_pi (2*3) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 2*3 = 6 := by decide
  rw [hk_eq]
  have hk : my_pi (6) = 3 := pi_6
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_3 (m : ℕ) (hm1 : m ≥ 1) : my_pi (3*4) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 3*4 = 12 := by decide
  rw [hk_eq]
  have hk : my_pi (12) = 5 := pi_12
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_4 (m : ℕ) (hm1 : m ≥ 1) : my_pi (4*5) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 4*5 = 20 := by decide
  rw [hk_eq]
  have hk : my_pi (20) = 8 := pi_20
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_5 (m : ℕ) (hm1 : m ≥ 1) : my_pi (5*6) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 5*6 = 30 := by decide
  rw [hk_eq]
  have hk : my_pi (30) = 10 := pi_30
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_6 (m : ℕ) (hm1 : m ≥ 1) : my_pi (6*7) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 6*7 = 42 := by decide
  rw [hk_eq]
  have hk : my_pi (42) = 13 := pi_42
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_7 (m : ℕ) (hm1 : m ≥ 1) : my_pi (7*8) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 7*8 = 56 := by decide
  rw [hk_eq]
  have hk : my_pi (56) = 16 := pi_56
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_8 (m : ℕ) (hm1 : m ≥ 1) : my_pi (8*9) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 8*9 = 72 := by decide
  rw [hk_eq]
  have hk : my_pi (72) = 20 := pi_72
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_9 (m : ℕ) (hm1 : m ≥ 1) : my_pi (9*10) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 9*10 = 90 := by decide
  rw [hk_eq]
  have hk : my_pi (90) = 24 := pi_90
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_10 (m : ℕ) (hm1 : m ≥ 1) : my_pi (10*11) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 10*11 = 110 := by decide
  rw [hk_eq]
  have hk : my_pi (110) = 29 := pi_110
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_11 (m : ℕ) (hm1 : m ≥ 1) : my_pi (11*12) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 11*12 = 132 := by decide
  rw [hk_eq]
  have hk : my_pi (132) = 32 := pi_132
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_12 (m : ℕ) (hm1 : m ≥ 1) : my_pi (12*13) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 12*13 = 156 := by decide
  rw [hk_eq]
  have hk : my_pi (156) = 36 := pi_156
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_13 (m : ℕ) (hm1 : m ≥ 1) : my_pi (13*14) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 13*14 = 182 := by decide
  rw [hk_eq]
  have hk : my_pi (182) = 42 := pi_182
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_14 (m : ℕ) (hm1 : m ≥ 1) : my_pi (14*15) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 14*15 = 210 := by decide
  rw [hk_eq]
  have hk : my_pi (210) = 46 := pi_210
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_15 (m : ℕ) (hm1 : m ≥ 1) : my_pi (15*16) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 15*16 = 240 := by decide
  rw [hk_eq]
  have hk : my_pi (240) = 52 := pi_240
  have hm0 : my_pi (626640) = 51098 := pi_626640
  have hm1_val : my_pi (627760) = 51179 := pi_627760
  rcases le_or_gt m 1119 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 626640 := bound_le_helper m 1119 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1120 ≤ m := hm_gt
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_16 (m : ℕ) (hm : m ≠ 1119) (hm1 : m ≥ 1) : my_pi (16*17) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 16*17 = 272 := by decide
  rw [hk_eq]
  have hk : my_pi (272) = 58 := pi_272
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm2 : my_pi (627760) = 51179 := pi_627760
  rcases lt_trichotomy m 1119 with hl | he | hg
  · have hl : m ≤ 1118 := by omega
    have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hl
    have h2 := my_pi_mono h1
    omega
  · contradiction
  · have hm_ge : 1120 ≤ m := by omega
    have h1 : 627760 ≤ m*(m+1)/2 := bound_gt_helper m 1120 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_17 (m : ℕ) (hm1 : m ≥ 1) : my_pi (17*18) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 17*18 = 306 := by decide
  rw [hk_eq]
  have hk : my_pi (306) = 62 := pi_306
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_18 (m : ℕ) (hm1 : m ≥ 1) : my_pi (18*19) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 18*19 = 342 := by decide
  rw [hk_eq]
  have hk : my_pi (342) = 68 := pi_342
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_19 (m : ℕ) (hm1 : m ≥ 1) : my_pi (19*20) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 19*20 = 380 := by decide
  rw [hk_eq]
  have hk : my_pi (380) = 75 := pi_380
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_20 (m : ℕ) (hm1 : m ≥ 1) : my_pi (20*21) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 20*21 = 420 := by decide
  rw [hk_eq]
  have hk : my_pi (420) = 81 := pi_420
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_21 (m : ℕ) (hm1 : m ≥ 1) : my_pi (21*22) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 21*22 = 462 := by decide
  rw [hk_eq]
  have hk : my_pi (462) = 89 := pi_462
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_22 (m : ℕ) (hm1 : m ≥ 1) : my_pi (22*23) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 22*23 = 506 := by decide
  rw [hk_eq]
  have hk : my_pi (506) = 96 := pi_506
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_23 (m : ℕ) (hm1 : m ≥ 1) : my_pi (23*24) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 23*24 = 552 := by decide
  rw [hk_eq]
  have hk : my_pi (552) = 101 := pi_552
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_24 (m : ℕ) (hm1 : m ≥ 1) : my_pi (24*25) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 24*25 = 600 := by decide
  rw [hk_eq]
  have hk : my_pi (600) = 109 := pi_600
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_25 (m : ℕ) (hm1 : m ≥ 1) : my_pi (25*26) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 25*26 = 650 := by decide
  rw [hk_eq]
  have hk : my_pi (650) = 118 := pi_650
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_26 (m : ℕ) (hm1 : m ≥ 1) : my_pi (26*27) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 26*27 = 702 := by decide
  rw [hk_eq]
  have hk : my_pi (702) = 126 := pi_702
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_27 (m : ℕ) (hm1 : m ≥ 1) : my_pi (27*28) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 27*28 = 756 := by decide
  rw [hk_eq]
  have hk : my_pi (756) = 133 := pi_756
  have hm0 : my_pi (625521) = 51022 := pi_625521
  have hm1_val : my_pi (626640) = 51098 := pi_626640
  rcases le_or_gt m 1118 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 625521 := bound_le_helper m 1118 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1119 ≤ m := hm_gt
    have h1 : 626640 ≤ m*(m+1)/2 := bound_gt_helper m 1119 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_28 (m : ℕ) (hm1 : m ≥ 1) : my_pi (28*29) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 28*29 = 812 := by decide
  rw [hk_eq]
  have hk : my_pi (812) = 141 := pi_812
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_29 (m : ℕ) (hm1 : m ≥ 1) : my_pi (29*30) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 29*30 = 870 := by decide
  rw [hk_eq]
  have hk : my_pi (870) = 150 := pi_870
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_30 (m : ℕ) (hm1 : m ≥ 1) : my_pi (30*31) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 30*31 = 930 := by decide
  rw [hk_eq]
  have hk : my_pi (930) = 158 := pi_930
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_31 (m : ℕ) (hm1 : m ≥ 1) : my_pi (31*32) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 31*32 = 992 := by decide
  rw [hk_eq]
  have hk : my_pi (992) = 167 := pi_992
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_32 (m : ℕ) (hm1 : m ≥ 1) : my_pi (32*33) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 32*33 = 1056 := by decide
  rw [hk_eq]
  have hk : my_pi (1056) = 177 := pi_1056
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_33 (m : ℕ) (hm1 : m ≥ 1) : my_pi (33*34) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 33*34 = 1122 := by decide
  rw [hk_eq]
  have hk : my_pi (1122) = 187 := pi_1122
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_34 (m : ℕ) (hm1 : m ≥ 1) : my_pi (34*35) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 34*35 = 1190 := by decide
  rw [hk_eq]
  have hk : my_pi (1190) = 195 := pi_1190
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_35 (m : ℕ) (hm1 : m ≥ 1) : my_pi (35*36) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 35*36 = 1260 := by decide
  rw [hk_eq]
  have hk : my_pi (1260) = 205 := pi_1260
  have hm0 : my_pi (624403) = 50940 := pi_624403
  have hm1_val : my_pi (625521) = 51022 := pi_625521
  rcases le_or_gt m 1117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 624403 := bound_le_helper m 1117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1118 ≤ m := hm_gt
    have h1 : 625521 ≤ m*(m+1)/2 := bound_gt_helper m 1118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_36 (m : ℕ) (hm1 : m ≥ 1) : my_pi (36*37) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 36*37 = 1332 := by decide
  rw [hk_eq]
  have hk : my_pi (1332) = 217 := pi_1332
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_37 (m : ℕ) (hm1 : m ≥ 1) : my_pi (37*38) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 37*38 = 1406 := by decide
  rw [hk_eq]
  have hk : my_pi (1406) = 222 := pi_1406
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_38 (m : ℕ) (hm1 : m ≥ 1) : my_pi (38*39) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 38*39 = 1482 := by decide
  rw [hk_eq]
  have hk : my_pi (1482) = 234 := pi_1482
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_39 (m : ℕ) (hm1 : m ≥ 1) : my_pi (39*40) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 39*40 = 1560 := by decide
  rw [hk_eq]
  have hk : my_pi (1560) = 246 := pi_1560
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_40 (m : ℕ) (hm1 : m ≥ 1) : my_pi (40*41) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 40*41 = 1640 := by decide
  rw [hk_eq]
  have hk : my_pi (1640) = 259 := pi_1640
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_41 (m : ℕ) (hm1 : m ≥ 1) : my_pi (41*42) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 41*42 = 1722 := by decide
  rw [hk_eq]
  have hk : my_pi (1722) = 268 := pi_1722
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_42 (m : ℕ) (hm1 : m ≥ 1) : my_pi (42*43) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 42*43 = 1806 := by decide
  rw [hk_eq]
  have hk : my_pi (1806) = 279 := pi_1806
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_43 (m : ℕ) (hm1 : m ≥ 1) : my_pi (43*44) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 43*44 = 1892 := by decide
  rw [hk_eq]
  have hk : my_pi (1892) = 290 := pi_1892
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_44 (m : ℕ) (hm1 : m ≥ 1) : my_pi (44*45) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 44*45 = 1980 := by decide
  rw [hk_eq]
  have hk : my_pi (1980) = 299 := pi_1980
  have hm0 : my_pi (623286) = 50850 := pi_623286
  have hm1_val : my_pi (624403) = 50940 := pi_624403
  rcases le_or_gt m 1116 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 623286 := bound_le_helper m 1116 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1117 ≤ m := hm_gt
    have h1 : 624403 ≤ m*(m+1)/2 := bound_gt_helper m 1117 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_45 (m : ℕ) (hm1 : m ≥ 1) : my_pi (45*46) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 45*46 = 2070 := by decide
  rw [hk_eq]
  have hk : my_pi (2070) = 312 := pi_2070
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_46 (m : ℕ) (hm1 : m ≥ 1) : my_pi (46*47) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 46*47 = 2162 := by decide
  rw [hk_eq]
  have hk : my_pi (2162) = 326 := pi_2162
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_47 (m : ℕ) (hm1 : m ≥ 1) : my_pi (47*48) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 47*48 = 2256 := by decide
  rw [hk_eq]
  have hk : my_pi (2256) = 335 := pi_2256
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_48 (m : ℕ) (hm1 : m ≥ 1) : my_pi (48*49) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 48*49 = 2352 := by decide
  rw [hk_eq]
  have hk : my_pi (2352) = 349 := pi_2352
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_49 (m : ℕ) (hm1 : m ≥ 1) : my_pi (49*50) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 49*50 = 2450 := by decide
  rw [hk_eq]
  have hk : my_pi (2450) = 363 := pi_2450
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_50 (m : ℕ) (hm1 : m ≥ 1) : my_pi (50*51) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 50*51 = 2550 := by decide
  rw [hk_eq]
  have hk : my_pi (2550) = 373 := pi_2550
  have hm0 : my_pi (622170) = 50775 := pi_622170
  have hm1_val : my_pi (623286) = 50850 := pi_623286
  rcases le_or_gt m 1115 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 622170 := bound_le_helper m 1115 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1116 ≤ m := hm_gt
    have h1 : 623286 ≤ m*(m+1)/2 := bound_gt_helper m 1116 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_51 (m : ℕ) (hm1 : m ≥ 1) : my_pi (51*52) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 51*52 = 2652 := by decide
  rw [hk_eq]
  have hk : my_pi (2652) = 383 := pi_2652
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_52 (m : ℕ) (hm1 : m ≥ 1) : my_pi (52*53) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 52*53 = 2756 := by decide
  rw [hk_eq]
  have hk : my_pi (2756) = 402 := pi_2756
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_53 (m : ℕ) (hm1 : m ≥ 1) : my_pi (53*54) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 53*54 = 2862 := by decide
  rw [hk_eq]
  have hk : my_pi (2862) = 416 := pi_2862
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_54 (m : ℕ) (hm1 : m ≥ 1) : my_pi (54*55) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 54*55 = 2970 := by decide
  rw [hk_eq]
  have hk : my_pi (2970) = 428 := pi_2970
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_55 (m : ℕ) (hm1 : m ≥ 1) : my_pi (55*56) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 55*56 = 3080 := by decide
  rw [hk_eq]
  have hk : my_pi (3080) = 440 := pi_3080
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_56 (m : ℕ) (hm1 : m ≥ 1) : my_pi (56*57) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 56*57 = 3192 := by decide
  rw [hk_eq]
  have hk : my_pi (3192) = 452 := pi_3192
  have hm0 : my_pi (621055) = 50695 := pi_621055
  have hm1_val : my_pi (622170) = 50775 := pi_622170
  rcases le_or_gt m 1114 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 621055 := bound_le_helper m 1114 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1115 ≤ m := hm_gt
    have h1 : 622170 ≤ m*(m+1)/2 := bound_gt_helper m 1115 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_57 (m : ℕ) (hm1 : m ≥ 1) : my_pi (57*58) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 57*58 = 3306 := by decide
  rw [hk_eq]
  have hk : my_pi (3306) = 464 := pi_3306
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_58 (m : ℕ) (hm1 : m ≥ 1) : my_pi (58*59) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 58*59 = 3422 := by decide
  rw [hk_eq]
  have hk : my_pi (3422) = 480 := pi_3422
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_59 (m : ℕ) (hm1 : m ≥ 1) : my_pi (59*60) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 59*60 = 3540 := by decide
  rw [hk_eq]
  have hk : my_pi (3540) = 495 := pi_3540
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_60 (m : ℕ) (hm1 : m ≥ 1) : my_pi (60*61) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 60*61 = 3660 := by decide
  rw [hk_eq]
  have hk : my_pi (3660) = 511 := pi_3660
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_61 (m : ℕ) (hm1 : m ≥ 1) : my_pi (61*62) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 61*62 = 3782 := by decide
  rw [hk_eq]
  have hk : my_pi (3782) = 526 := pi_3782
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_62 (m : ℕ) (hm1 : m ≥ 1) : my_pi (62*63) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 62*63 = 3906 := by decide
  rw [hk_eq]
  have hk : my_pi (3906) = 539 := pi_3906
  have hm0 : my_pi (619941) = 50607 := pi_619941
  have hm1_val : my_pi (621055) = 50695 := pi_621055
  rcases le_or_gt m 1113 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 619941 := bound_le_helper m 1113 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1114 ≤ m := hm_gt
    have h1 : 621055 ≤ m*(m+1)/2 := bound_gt_helper m 1114 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_63 (m : ℕ) (hm1 : m ≥ 1) : my_pi (63*64) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 63*64 = 4032 := by decide
  rw [hk_eq]
  have hk : my_pi (4032) = 557 := pi_4032
  have hm0 : my_pi (618828) = 50525 := pi_618828
  have hm1_val : my_pi (619941) = 50607 := pi_619941
  rcases le_or_gt m 1112 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 618828 := bound_le_helper m 1112 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1113 ≤ m := hm_gt
    have h1 : 619941 ≤ m*(m+1)/2 := bound_gt_helper m 1113 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_64 (m : ℕ) (hm1 : m ≥ 1) : my_pi (64*65) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 64*65 = 4160 := by decide
  rw [hk_eq]
  have hk : my_pi (4160) = 573 := pi_4160
  have hm0 : my_pi (618828) = 50525 := pi_618828
  have hm1_val : my_pi (619941) = 50607 := pi_619941
  rcases le_or_gt m 1112 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 618828 := bound_le_helper m 1112 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1113 ≤ m := hm_gt
    have h1 : 619941 ≤ m*(m+1)/2 := bound_gt_helper m 1113 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_65 (m : ℕ) (hm1 : m ≥ 1) : my_pi (65*66) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 65*66 = 4290 := by decide
  rw [hk_eq]
  have hk : my_pi (4290) = 589 := pi_4290
  have hm0 : my_pi (618828) = 50525 := pi_618828
  have hm1_val : my_pi (619941) = 50607 := pi_619941
  rcases le_or_gt m 1112 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 618828 := bound_le_helper m 1112 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1113 ≤ m := hm_gt
    have h1 : 619941 ≤ m*(m+1)/2 := bound_gt_helper m 1113 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_66 (m : ℕ) (hm1 : m ≥ 1) : my_pi (66*67) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 66*67 = 4422 := by decide
  rw [hk_eq]
  have hk : my_pi (4422) = 601 := pi_4422
  have hm0 : my_pi (618828) = 50525 := pi_618828
  have hm1_val : my_pi (619941) = 50607 := pi_619941
  rcases le_or_gt m 1112 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 618828 := bound_le_helper m 1112 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1113 ≤ m := hm_gt
    have h1 : 619941 ≤ m*(m+1)/2 := bound_gt_helper m 1113 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_67 (m : ℕ) (hm1 : m ≥ 1) : my_pi (67*68) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 67*68 = 4556 := by decide
  rw [hk_eq]
  have hk : my_pi (4556) = 617 := pi_4556
  have hm0 : my_pi (618828) = 50525 := pi_618828
  have hm1_val : my_pi (619941) = 50607 := pi_619941
  rcases le_or_gt m 1112 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 618828 := bound_le_helper m 1112 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1113 ≤ m := hm_gt
    have h1 : 619941 ≤ m*(m+1)/2 := bound_gt_helper m 1113 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_68 (m : ℕ) (hm1 : m ≥ 1) : my_pi (68*69) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 68*69 = 4692 := by decide
  rw [hk_eq]
  have hk : my_pi (4692) = 634 := pi_4692
  have hm0 : my_pi (617716) = 50449 := pi_617716
  have hm1_val : my_pi (618828) = 50525 := pi_618828
  rcases le_or_gt m 1111 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 617716 := bound_le_helper m 1111 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1112 ≤ m := hm_gt
    have h1 : 618828 ≤ m*(m+1)/2 := bound_gt_helper m 1112 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_69 (m : ℕ) (hm1 : m ≥ 1) : my_pi (69*70) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 69*70 = 4830 := by decide
  rw [hk_eq]
  have hk : my_pi (4830) = 649 := pi_4830
  have hm0 : my_pi (617716) = 50449 := pi_617716
  have hm1_val : my_pi (618828) = 50525 := pi_618828
  rcases le_or_gt m 1111 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 617716 := bound_le_helper m 1111 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1112 ≤ m := hm_gt
    have h1 : 618828 ≤ m*(m+1)/2 := bound_gt_helper m 1112 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_70 (m : ℕ) (hm1 : m ≥ 1) : my_pi (70*71) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 70*71 = 4970 := by decide
  rw [hk_eq]
  have hk : my_pi (4970) = 665 := pi_4970
  have hm0 : my_pi (617716) = 50449 := pi_617716
  have hm1_val : my_pi (618828) = 50525 := pi_618828
  rcases le_or_gt m 1111 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 617716 := bound_le_helper m 1111 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1112 ≤ m := hm_gt
    have h1 : 618828 ≤ m*(m+1)/2 := bound_gt_helper m 1112 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_71 (m : ℕ) (hm1 : m ≥ 1) : my_pi (71*72) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 71*72 = 5112 := by decide
  rw [hk_eq]
  have hk : my_pi (5112) = 683 := pi_5112
  have hm0 : my_pi (617716) = 50449 := pi_617716
  have hm1_val : my_pi (618828) = 50525 := pi_618828
  rcases le_or_gt m 1111 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 617716 := bound_le_helper m 1111 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1112 ≤ m := hm_gt
    have h1 : 618828 ≤ m*(m+1)/2 := bound_gt_helper m 1112 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_72 (m : ℕ) (hm1 : m ≥ 1) : my_pi (72*73) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 72*73 = 5256 := by decide
  rw [hk_eq]
  have hk : my_pi (5256) = 697 := pi_5256
  have hm0 : my_pi (617716) = 50449 := pi_617716
  have hm1_val : my_pi (618828) = 50525 := pi_618828
  rcases le_or_gt m 1111 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 617716 := bound_le_helper m 1111 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1112 ≤ m := hm_gt
    have h1 : 618828 ≤ m*(m+1)/2 := bound_gt_helper m 1112 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_73 (m : ℕ) (hm1 : m ≥ 1) : my_pi (73*74) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 73*74 = 5402 := by decide
  rw [hk_eq]
  have hk : my_pi (5402) = 712 := pi_5402
  have hm0 : my_pi (616605) = 50360 := pi_616605
  have hm1_val : my_pi (617716) = 50449 := pi_617716
  rcases le_or_gt m 1110 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 616605 := bound_le_helper m 1110 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1111 ≤ m := hm_gt
    have h1 : 617716 ≤ m*(m+1)/2 := bound_gt_helper m 1111 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_74 (m : ℕ) (hm1 : m ≥ 1) : my_pi (74*75) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 74*75 = 5550 := by decide
  rw [hk_eq]
  have hk : my_pi (5550) = 732 := pi_5550
  have hm0 : my_pi (616605) = 50360 := pi_616605
  have hm1_val : my_pi (617716) = 50449 := pi_617716
  rcases le_or_gt m 1110 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 616605 := bound_le_helper m 1110 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1111 ≤ m := hm_gt
    have h1 : 617716 ≤ m*(m+1)/2 := bound_gt_helper m 1111 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_75 (m : ℕ) (hm1 : m ≥ 1) : my_pi (75*76) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 75*76 = 5700 := by decide
  rw [hk_eq]
  have hk : my_pi (5700) = 750 := pi_5700
  have hm0 : my_pi (616605) = 50360 := pi_616605
  have hm1_val : my_pi (617716) = 50449 := pi_617716
  rcases le_or_gt m 1110 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 616605 := bound_le_helper m 1110 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1111 ≤ m := hm_gt
    have h1 : 617716 ≤ m*(m+1)/2 := bound_gt_helper m 1111 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_76 (m : ℕ) (hm1 : m ≥ 1) : my_pi (76*77) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 76*77 = 5852 := by decide
  rw [hk_eq]
  have hk : my_pi (5852) = 769 := pi_5852
  have hm0 : my_pi (616605) = 50360 := pi_616605
  have hm1_val : my_pi (617716) = 50449 := pi_617716
  rcases le_or_gt m 1110 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 616605 := bound_le_helper m 1110 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1111 ≤ m := hm_gt
    have h1 : 617716 ≤ m*(m+1)/2 := bound_gt_helper m 1111 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_77 (m : ℕ) (hm1 : m ≥ 1) : my_pi (77*78) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 77*78 = 6006 := by decide
  rw [hk_eq]
  have hk : my_pi (6006) = 783 := pi_6006
  have hm0 : my_pi (616605) = 50360 := pi_616605
  have hm1_val : my_pi (617716) = 50449 := pi_617716
  rcases le_or_gt m 1110 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 616605 := bound_le_helper m 1110 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1111 ≤ m := hm_gt
    have h1 : 617716 ≤ m*(m+1)/2 := bound_gt_helper m 1111 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_78 (m : ℕ) (hm1 : m ≥ 1) : my_pi (78*79) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 78*79 = 6162 := by decide
  rw [hk_eq]
  have hk : my_pi (6162) = 802 := pi_6162
  have hm0 : my_pi (615495) = 50268 := pi_615495
  have hm1_val : my_pi (616605) = 50360 := pi_616605
  rcases le_or_gt m 1109 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 615495 := bound_le_helper m 1109 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1110 ≤ m := hm_gt
    have h1 : 616605 ≤ m*(m+1)/2 := bound_gt_helper m 1110 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_79 (m : ℕ) (hm1 : m ≥ 1) : my_pi (79*80) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 79*80 = 6320 := by decide
  rw [hk_eq]
  have hk : my_pi (6320) = 822 := pi_6320
  have hm0 : my_pi (615495) = 50268 := pi_615495
  have hm1_val : my_pi (616605) = 50360 := pi_616605
  rcases le_or_gt m 1109 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 615495 := bound_le_helper m 1109 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1110 ≤ m := hm_gt
    have h1 : 616605 ≤ m*(m+1)/2 := bound_gt_helper m 1110 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_80 (m : ℕ) (hm1 : m ≥ 1) : my_pi (80*81) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 80*81 = 6480 := by decide
  rw [hk_eq]
  have hk : my_pi (6480) = 840 := pi_6480
  have hm0 : my_pi (615495) = 50268 := pi_615495
  have hm1_val : my_pi (616605) = 50360 := pi_616605
  rcases le_or_gt m 1109 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 615495 := bound_le_helper m 1109 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1110 ≤ m := hm_gt
    have h1 : 616605 ≤ m*(m+1)/2 := bound_gt_helper m 1110 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_81 (m : ℕ) (hm1 : m ≥ 1) : my_pi (81*82) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 81*82 = 6642 := by decide
  rw [hk_eq]
  have hk : my_pi (6642) = 856 := pi_6642
  have hm0 : my_pi (615495) = 50268 := pi_615495
  have hm1_val : my_pi (616605) = 50360 := pi_616605
  rcases le_or_gt m 1109 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 615495 := bound_le_helper m 1109 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1110 ≤ m := hm_gt
    have h1 : 616605 ≤ m*(m+1)/2 := bound_gt_helper m 1110 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_82 (m : ℕ) (hm1 : m ≥ 1) : my_pi (82*83) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 82*83 = 6806 := by decide
  rw [hk_eq]
  have hk : my_pi (6806) = 876 := pi_6806
  have hm0 : my_pi (615495) = 50268 := pi_615495
  have hm1_val : my_pi (616605) = 50360 := pi_616605
  rcases le_or_gt m 1109 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 615495 := bound_le_helper m 1109 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1110 ≤ m := hm_gt
    have h1 : 616605 ≤ m*(m+1)/2 := bound_gt_helper m 1110 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_83 (m : ℕ) (hm1 : m ≥ 1) : my_pi (83*84) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 83*84 = 6972 := by decide
  rw [hk_eq]
  have hk : my_pi (6972) = 896 := pi_6972
  have hm0 : my_pi (614386) = 50184 := pi_614386
  have hm1_val : my_pi (615495) = 50268 := pi_615495
  rcases le_or_gt m 1108 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 614386 := bound_le_helper m 1108 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1109 ≤ m := hm_gt
    have h1 : 615495 ≤ m*(m+1)/2 := bound_gt_helper m 1109 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_84 (m : ℕ) (hm1 : m ≥ 1) : my_pi (84*85) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 84*85 = 7140 := by decide
  rw [hk_eq]
  have hk : my_pi (7140) = 914 := pi_7140
  have hm0 : my_pi (614386) = 50184 := pi_614386
  have hm1_val : my_pi (615495) = 50268 := pi_615495
  rcases le_or_gt m 1108 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 614386 := bound_le_helper m 1108 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1109 ≤ m := hm_gt
    have h1 : 615495 ≤ m*(m+1)/2 := bound_gt_helper m 1109 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_85 (m : ℕ) (hm1 : m ≥ 1) : my_pi (85*86) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 85*86 = 7310 := by decide
  rw [hk_eq]
  have hk : my_pi (7310) = 932 := pi_7310
  have hm0 : my_pi (614386) = 50184 := pi_614386
  have hm1_val : my_pi (615495) = 50268 := pi_615495
  rcases le_or_gt m 1108 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 614386 := bound_le_helper m 1108 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1109 ≤ m := hm_gt
    have h1 : 615495 ≤ m*(m+1)/2 := bound_gt_helper m 1109 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_86 (m : ℕ) (hm1 : m ≥ 1) : my_pi (86*87) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 86*87 = 7482 := by decide
  rw [hk_eq]
  have hk : my_pi (7482) = 947 := pi_7482
  have hm0 : my_pi (614386) = 50184 := pi_614386
  have hm1_val : my_pi (615495) = 50268 := pi_615495
  rcases le_or_gt m 1108 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 614386 := bound_le_helper m 1108 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1109 ≤ m := hm_gt
    have h1 : 615495 ≤ m*(m+1)/2 := bound_gt_helper m 1109 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_87 (m : ℕ) (hm1 : m ≥ 1) : my_pi (87*88) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 87*88 = 7656 := by decide
  rw [hk_eq]
  have hk : my_pi (7656) = 971 := pi_7656
  have hm0 : my_pi (614386) = 50184 := pi_614386
  have hm1_val : my_pi (615495) = 50268 := pi_615495
  rcases le_or_gt m 1108 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 614386 := bound_le_helper m 1108 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1109 ≤ m := hm_gt
    have h1 : 615495 ≤ m*(m+1)/2 := bound_gt_helper m 1109 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_88 (m : ℕ) (hm1 : m ≥ 1) : my_pi (88*89) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 88*89 = 7832 := by decide
  rw [hk_eq]
  have hk : my_pi (7832) = 990 := pi_7832
  have hm0 : my_pi (613278) = 50104 := pi_613278
  have hm1_val : my_pi (614386) = 50184 := pi_614386
  rcases le_or_gt m 1107 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 613278 := bound_le_helper m 1107 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1108 ≤ m := hm_gt
    have h1 : 614386 ≤ m*(m+1)/2 := bound_gt_helper m 1108 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_89 (m : ℕ) (hm1 : m ≥ 1) : my_pi (89*90) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 89*90 = 8010 := by decide
  rw [hk_eq]
  have hk : my_pi (8010) = 1008 := pi_8010
  have hm0 : my_pi (613278) = 50104 := pi_613278
  have hm1_val : my_pi (614386) = 50184 := pi_614386
  rcases le_or_gt m 1107 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 613278 := bound_le_helper m 1107 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1108 ≤ m := hm_gt
    have h1 : 614386 ≤ m*(m+1)/2 := bound_gt_helper m 1108 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_90 (m : ℕ) (hm1 : m ≥ 1) : my_pi (90*91) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 90*91 = 8190 := by decide
  rw [hk_eq]
  have hk : my_pi (8190) = 1027 := pi_8190
  have hm0 : my_pi (613278) = 50104 := pi_613278
  have hm1_val : my_pi (614386) = 50184 := pi_614386
  rcases le_or_gt m 1107 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 613278 := bound_le_helper m 1107 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1108 ≤ m := hm_gt
    have h1 : 614386 ≤ m*(m+1)/2 := bound_gt_helper m 1108 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_91 (m : ℕ) (hm1 : m ≥ 1) : my_pi (91*92) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 91*92 = 8372 := by decide
  rw [hk_eq]
  have hk : my_pi (8372) = 1048 := pi_8372
  have hm0 : my_pi (613278) = 50104 := pi_613278
  have hm1_val : my_pi (614386) = 50184 := pi_614386
  rcases le_or_gt m 1107 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 613278 := bound_le_helper m 1107 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1108 ≤ m := hm_gt
    have h1 : 614386 ≤ m*(m+1)/2 := bound_gt_helper m 1108 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_92 (m : ℕ) (hm1 : m ≥ 1) : my_pi (92*93) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 92*93 = 8556 := by decide
  rw [hk_eq]
  have hk : my_pi (8556) = 1066 := pi_8556
  have hm0 : my_pi (612171) = 50022 := pi_612171
  have hm1_val : my_pi (613278) = 50104 := pi_613278
  rcases le_or_gt m 1106 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 612171 := bound_le_helper m 1106 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1107 ≤ m := hm_gt
    have h1 : 613278 ≤ m*(m+1)/2 := bound_gt_helper m 1107 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_93 (m : ℕ) (hm1 : m ≥ 1) : my_pi (93*94) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 93*94 = 8742 := by decide
  rw [hk_eq]
  have hk : my_pi (8742) = 1090 := pi_8742
  have hm0 : my_pi (612171) = 50022 := pi_612171
  have hm1_val : my_pi (613278) = 50104 := pi_613278
  rcases le_or_gt m 1106 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 612171 := bound_le_helper m 1106 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1107 ≤ m := hm_gt
    have h1 : 613278 ≤ m*(m+1)/2 := bound_gt_helper m 1107 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_94 (m : ℕ) (hm1 : m ≥ 1) : my_pi (94*95) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 94*95 = 8930 := by decide
  rw [hk_eq]
  have hk : my_pi (8930) = 1110 := pi_8930
  have hm0 : my_pi (612171) = 50022 := pi_612171
  have hm1_val : my_pi (613278) = 50104 := pi_613278
  rcases le_or_gt m 1106 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 612171 := bound_le_helper m 1106 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1107 ≤ m := hm_gt
    have h1 : 613278 ≤ m*(m+1)/2 := bound_gt_helper m 1107 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_95 (m : ℕ) (hm1 : m ≥ 1) : my_pi (95*96) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 95*96 = 9120 := by decide
  rw [hk_eq]
  have hk : my_pi (9120) = 1130 := pi_9120
  have hm0 : my_pi (612171) = 50022 := pi_612171
  have hm1_val : my_pi (613278) = 50104 := pi_613278
  rcases le_or_gt m 1106 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 612171 := bound_le_helper m 1106 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1107 ≤ m := hm_gt
    have h1 : 613278 ≤ m*(m+1)/2 := bound_gt_helper m 1107 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_96 (m : ℕ) (hm1 : m ≥ 1) : my_pi (96*97) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 96*97 = 9312 := by decide
  rw [hk_eq]
  have hk : my_pi (9312) = 1152 := pi_9312
  have hm0 : my_pi (611065) = 49938 := pi_611065
  have hm1_val : my_pi (612171) = 50022 := pi_612171
  rcases le_or_gt m 1105 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 611065 := bound_le_helper m 1105 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1106 ≤ m := hm_gt
    have h1 : 612171 ≤ m*(m+1)/2 := bound_gt_helper m 1106 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_97 (m : ℕ) (hm1 : m ≥ 1) : my_pi (97*98) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 97*98 = 9506 := by decide
  rw [hk_eq]
  have hk : my_pi (9506) = 1177 := pi_9506
  have hm0 : my_pi (611065) = 49938 := pi_611065
  have hm1_val : my_pi (612171) = 50022 := pi_612171
  rcases le_or_gt m 1105 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 611065 := bound_le_helper m 1105 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1106 ≤ m := hm_gt
    have h1 : 612171 ≤ m*(m+1)/2 := bound_gt_helper m 1106 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_98 (m : ℕ) (hm1 : m ≥ 1) : my_pi (98*99) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 98*99 = 9702 := by decide
  rw [hk_eq]
  have hk : my_pi (9702) = 1197 := pi_9702
  have hm0 : my_pi (611065) = 49938 := pi_611065
  have hm1_val : my_pi (612171) = 50022 := pi_612171
  rcases le_or_gt m 1105 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 611065 := bound_le_helper m 1105 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1106 ≤ m := hm_gt
    have h1 : 612171 ≤ m*(m+1)/2 := bound_gt_helper m 1106 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_99 (m : ℕ) (hm1 : m ≥ 1) : my_pi (99*100) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 99*100 = 9900 := by decide
  rw [hk_eq]
  have hk : my_pi (9900) = 1220 := pi_9900
  have hm0 : my_pi (609960) = 49857 := pi_609960
  have hm1_val : my_pi (611065) = 49938 := pi_611065
  rcases le_or_gt m 1104 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 609960 := bound_le_helper m 1104 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1105 ≤ m := hm_gt
    have h1 : 611065 ≤ m*(m+1)/2 := bound_gt_helper m 1105 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_100 (m : ℕ) (hm1 : m ≥ 1) : my_pi (100*101) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 100*101 = 10100 := by decide
  rw [hk_eq]
  have hk : my_pi (10100) = 1240 := pi_10100
  have hm0 : my_pi (609960) = 49857 := pi_609960
  have hm1_val : my_pi (611065) = 49938 := pi_611065
  rcases le_or_gt m 1104 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 609960 := bound_le_helper m 1104 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1105 ≤ m := hm_gt
    have h1 : 611065 ≤ m*(m+1)/2 := bound_gt_helper m 1105 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_101 (m : ℕ) (hm1 : m ≥ 1) : my_pi (101*102) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 101*102 = 10302 := by decide
  rw [hk_eq]
  have hk : my_pi (10302) = 1263 := pi_10302
  have hm0 : my_pi (609960) = 49857 := pi_609960
  have hm1_val : my_pi (611065) = 49938 := pi_611065
  rcases le_or_gt m 1104 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 609960 := bound_le_helper m 1104 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1105 ≤ m := hm_gt
    have h1 : 611065 ≤ m*(m+1)/2 := bound_gt_helper m 1105 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_102 (m : ℕ) (hm1 : m ≥ 1) : my_pi (102*103) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 102*103 = 10506 := by decide
  rw [hk_eq]
  have hk : my_pi (10506) = 1285 := pi_10506
  have hm0 : my_pi (609960) = 49857 := pi_609960
  have hm1_val : my_pi (611065) = 49938 := pi_611065
  rcases le_or_gt m 1104 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 609960 := bound_le_helper m 1104 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1105 ≤ m := hm_gt
    have h1 : 611065 ≤ m*(m+1)/2 := bound_gt_helper m 1105 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_103 (m : ℕ) (hm1 : m ≥ 1) : my_pi (103*104) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 103*104 = 10712 := by decide
  rw [hk_eq]
  have hk : my_pi (10712) = 1306 := pi_10712
  have hm0 : my_pi (608856) = 49767 := pi_608856
  have hm1_val : my_pi (609960) = 49857 := pi_609960
  rcases le_or_gt m 1103 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 608856 := bound_le_helper m 1103 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1104 ≤ m := hm_gt
    have h1 : 609960 ≤ m*(m+1)/2 := bound_gt_helper m 1104 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_104 (m : ℕ) (hm1 : m ≥ 1) : my_pi (104*105) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 104*105 = 10920 := by decide
  rw [hk_eq]
  have hk : my_pi (10920) = 1327 := pi_10920
  have hm0 : my_pi (608856) = 49767 := pi_608856
  have hm1_val : my_pi (609960) = 49857 := pi_609960
  rcases le_or_gt m 1103 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 608856 := bound_le_helper m 1103 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1104 ≤ m := hm_gt
    have h1 : 609960 ≤ m*(m+1)/2 := bound_gt_helper m 1104 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_105 (m : ℕ) (hm1 : m ≥ 1) : my_pi (105*106) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 105*106 = 11130 := by decide
  rw [hk_eq]
  have hk : my_pi (11130) = 1348 := pi_11130
  have hm0 : my_pi (608856) = 49767 := pi_608856
  have hm1_val : my_pi (609960) = 49857 := pi_609960
  rcases le_or_gt m 1103 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 608856 := bound_le_helper m 1103 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1104 ≤ m := hm_gt
    have h1 : 609960 ≤ m*(m+1)/2 := bound_gt_helper m 1104 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_106 (m : ℕ) (hm1 : m ≥ 1) : my_pi (106*107) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 106*107 = 11342 := by decide
  rw [hk_eq]
  have hk : my_pi (11342) = 1370 := pi_11342
  have hm0 : my_pi (608856) = 49767 := pi_608856
  have hm1_val : my_pi (609960) = 49857 := pi_609960
  rcases le_or_gt m 1103 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 608856 := bound_le_helper m 1103 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1104 ≤ m := hm_gt
    have h1 : 609960 ≤ m*(m+1)/2 := bound_gt_helper m 1104 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_107 (m : ℕ) (hm1 : m ≥ 1) : my_pi (107*108) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 107*108 = 11556 := by decide
  rw [hk_eq]
  have hk : my_pi (11556) = 1392 := pi_11556
  have hm0 : my_pi (607753) = 49684 := pi_607753
  have hm1_val : my_pi (608856) = 49767 := pi_608856
  rcases le_or_gt m 1102 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 607753 := bound_le_helper m 1102 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1103 ≤ m := hm_gt
    have h1 : 608856 ≤ m*(m+1)/2 := bound_gt_helper m 1103 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_108 (m : ℕ) (hm1 : m ≥ 1) : my_pi (108*109) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 108*109 = 11772 := by decide
  rw [hk_eq]
  have hk : my_pi (11772) = 1409 := pi_11772
  have hm0 : my_pi (607753) = 49684 := pi_607753
  have hm1_val : my_pi (608856) = 49767 := pi_608856
  rcases le_or_gt m 1102 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 607753 := bound_le_helper m 1102 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1103 ≤ m := hm_gt
    have h1 : 608856 ≤ m*(m+1)/2 := bound_gt_helper m 1103 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_109 (m : ℕ) (hm1 : m ≥ 1) : my_pi (109*110) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 109*110 = 11990 := by decide
  rw [hk_eq]
  have hk : my_pi (11990) = 1438 := pi_11990
  have hm0 : my_pi (607753) = 49684 := pi_607753
  have hm1_val : my_pi (608856) = 49767 := pi_608856
  rcases le_or_gt m 1102 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 607753 := bound_le_helper m 1102 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1103 ≤ m := hm_gt
    have h1 : 608856 ≤ m*(m+1)/2 := bound_gt_helper m 1103 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_110 (m : ℕ) (hm1 : m ≥ 1) : my_pi (110*111) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 110*111 = 12210 := by decide
  rw [hk_eq]
  have hk : my_pi (12210) = 1459 := pi_12210
  have hm0 : my_pi (607753) = 49684 := pi_607753
  have hm1_val : my_pi (608856) = 49767 := pi_608856
  rcases le_or_gt m 1102 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 607753 := bound_le_helper m 1102 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1103 ≤ m := hm_gt
    have h1 : 608856 ≤ m*(m+1)/2 := bound_gt_helper m 1103 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_111 (m : ℕ) (hm1 : m ≥ 1) : my_pi (111*112) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 111*112 = 12432 := by decide
  rw [hk_eq]
  have hk : my_pi (12432) = 1483 := pi_12432
  have hm0 : my_pi (606651) = 49599 := pi_606651
  have hm1_val : my_pi (607753) = 49684 := pi_607753
  rcases le_or_gt m 1101 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 606651 := bound_le_helper m 1101 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1102 ≤ m := hm_gt
    have h1 : 607753 ≤ m*(m+1)/2 := bound_gt_helper m 1102 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_112 (m : ℕ) (hm1 : m ≥ 1) : my_pi (112*113) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 112*113 = 12656 := by decide
  rw [hk_eq]
  have hk : my_pi (12656) = 1512 := pi_12656
  have hm0 : my_pi (606651) = 49599 := pi_606651
  have hm1_val : my_pi (607753) = 49684 := pi_607753
  rcases le_or_gt m 1101 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 606651 := bound_le_helper m 1101 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1102 ≤ m := hm_gt
    have h1 : 607753 ≤ m*(m+1)/2 := bound_gt_helper m 1102 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_113 (m : ℕ) (hm1 : m ≥ 1) : my_pi (113*114) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 113*114 = 12882 := by decide
  rw [hk_eq]
  have hk : my_pi (12882) = 1532 := pi_12882
  have hm0 : my_pi (606651) = 49599 := pi_606651
  have hm1_val : my_pi (607753) = 49684 := pi_607753
  rcases le_or_gt m 1101 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 606651 := bound_le_helper m 1101 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1102 ≤ m := hm_gt
    have h1 : 607753 ≤ m*(m+1)/2 := bound_gt_helper m 1102 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_114 (m : ℕ) (hm1 : m ≥ 1) : my_pi (114*115) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 114*115 = 13110 := by decide
  rw [hk_eq]
  have hk : my_pi (13110) = 1560 := pi_13110
  have hm0 : my_pi (605550) = 49520 := pi_605550
  have hm1_val : my_pi (606651) = 49599 := pi_606651
  rcases le_or_gt m 1100 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 605550 := bound_le_helper m 1100 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1101 ≤ m := hm_gt
    have h1 : 606651 ≤ m*(m+1)/2 := bound_gt_helper m 1101 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_115 (m : ℕ) (hm1 : m ≥ 1) : my_pi (115*116) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 115*116 = 13340 := by decide
  rw [hk_eq]
  have hk : my_pi (13340) = 1585 := pi_13340
  have hm0 : my_pi (605550) = 49520 := pi_605550
  have hm1_val : my_pi (606651) = 49599 := pi_606651
  rcases le_or_gt m 1100 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 605550 := bound_le_helper m 1100 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1101 ≤ m := hm_gt
    have h1 : 606651 ≤ m*(m+1)/2 := bound_gt_helper m 1101 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_116 (m : ℕ) (hm1 : m ≥ 1) : my_pi (116*117) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 116*117 = 13572 := by decide
  rw [hk_eq]
  have hk : my_pi (13572) = 1605 := pi_13572
  have hm0 : my_pi (605550) = 49520 := pi_605550
  have hm1_val : my_pi (606651) = 49599 := pi_606651
  rcases le_or_gt m 1100 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 605550 := bound_le_helper m 1100 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1101 ≤ m := hm_gt
    have h1 : 606651 ≤ m*(m+1)/2 := bound_gt_helper m 1101 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_117 (m : ℕ) (hm1 : m ≥ 1) : my_pi (117*118) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 117*118 = 13806 := by decide
  rw [hk_eq]
  have hk : my_pi (13806) = 1632 := pi_13806
  have hm0 : my_pi (605550) = 49520 := pi_605550
  have hm1_val : my_pi (606651) = 49599 := pi_606651
  rcases le_or_gt m 1100 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 605550 := bound_le_helper m 1100 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1101 ≤ m := hm_gt
    have h1 : 606651 ≤ m*(m+1)/2 := bound_gt_helper m 1101 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_118 (m : ℕ) (hm1 : m ≥ 1) : my_pi (118*119) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 118*119 = 14042 := by decide
  rw [hk_eq]
  have hk : my_pi (14042) = 1656 := pi_14042
  have hm0 : my_pi (604450) = 49437 := pi_604450
  have hm1_val : my_pi (605550) = 49520 := pi_605550
  rcases le_or_gt m 1099 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 604450 := bound_le_helper m 1099 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1100 ≤ m := hm_gt
    have h1 : 605550 ≤ m*(m+1)/2 := bound_gt_helper m 1100 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_119 (m : ℕ) (hm1 : m ≥ 1) : my_pi (119*120) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 119*120 = 14280 := by decide
  rw [hk_eq]
  have hk : my_pi (14280) = 1675 := pi_14280
  have hm0 : my_pi (604450) = 49437 := pi_604450
  have hm1_val : my_pi (605550) = 49520 := pi_605550
  rcases le_or_gt m 1099 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 604450 := bound_le_helper m 1099 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1100 ≤ m := hm_gt
    have h1 : 605550 ≤ m*(m+1)/2 := bound_gt_helper m 1100 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_120 (m : ℕ) (hm1 : m ≥ 1) : my_pi (120*121) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 120*121 = 14520 := by decide
  rw [hk_eq]
  have hk : my_pi (14520) = 1700 := pi_14520
  have hm0 : my_pi (604450) = 49437 := pi_604450
  have hm1_val : my_pi (605550) = 49520 := pi_605550
  rcases le_or_gt m 1099 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 604450 := bound_le_helper m 1099 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1100 ≤ m := hm_gt
    have h1 : 605550 ≤ m*(m+1)/2 := bound_gt_helper m 1100 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_121 (m : ℕ) (hm1 : m ≥ 1) : my_pi (121*122) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 121*122 = 14762 := by decide
  rw [hk_eq]
  have hk : my_pi (14762) = 1729 := pi_14762
  have hm0 : my_pi (603351) = 49352 := pi_603351
  have hm1_val : my_pi (604450) = 49437 := pi_604450
  rcases le_or_gt m 1098 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 603351 := bound_le_helper m 1098 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1099 ≤ m := hm_gt
    have h1 : 604450 ≤ m*(m+1)/2 := bound_gt_helper m 1099 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_122 (m : ℕ) (hm1 : m ≥ 1) : my_pi (122*123) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 122*123 = 15006 := by decide
  rw [hk_eq]
  have hk : my_pi (15006) = 1754 := pi_15006
  have hm0 : my_pi (603351) = 49352 := pi_603351
  have hm1_val : my_pi (604450) = 49437 := pi_604450
  rcases le_or_gt m 1098 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 603351 := bound_le_helper m 1098 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1099 ≤ m := hm_gt
    have h1 : 604450 ≤ m*(m+1)/2 := bound_gt_helper m 1099 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_123 (m : ℕ) (hm1 : m ≥ 1) : my_pi (123*124) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 123*124 = 15252 := by decide
  rw [hk_eq]
  have hk : my_pi (15252) = 1779 := pi_15252
  have hm0 : my_pi (603351) = 49352 := pi_603351
  have hm1_val : my_pi (604450) = 49437 := pi_604450
  rcases le_or_gt m 1098 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 603351 := bound_le_helper m 1098 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1099 ≤ m := hm_gt
    have h1 : 604450 ≤ m*(m+1)/2 := bound_gt_helper m 1099 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_124 (m : ℕ) (hm1 : m ≥ 1) : my_pi (124*125) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 124*125 = 15500 := by decide
  rw [hk_eq]
  have hk : my_pi (15500) = 1810 := pi_15500
  have hm0 : my_pi (602253) = 49268 := pi_602253
  have hm1_val : my_pi (603351) = 49352 := pi_603351
  rcases le_or_gt m 1097 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 602253 := bound_le_helper m 1097 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1098 ≤ m := hm_gt
    have h1 : 603351 ≤ m*(m+1)/2 := bound_gt_helper m 1098 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_125 (m : ℕ) (hm1 : m ≥ 1) : my_pi (125*126) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 125*126 = 15750 := by decide
  rw [hk_eq]
  have hk : my_pi (15750) = 1837 := pi_15750
  have hm0 : my_pi (602253) = 49268 := pi_602253
  have hm1_val : my_pi (603351) = 49352 := pi_603351
  rcases le_or_gt m 1097 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 602253 := bound_le_helper m 1097 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1098 ≤ m := hm_gt
    have h1 : 603351 ≤ m*(m+1)/2 := bound_gt_helper m 1098 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_126 (m : ℕ) (hm1 : m ≥ 1) : my_pi (126*127) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 126*127 = 16002 := by decide
  rw [hk_eq]
  have hk : my_pi (16002) = 1863 := pi_16002
  have hm0 : my_pi (602253) = 49268 := pi_602253
  have hm1_val : my_pi (603351) = 49352 := pi_603351
  rcases le_or_gt m 1097 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 602253 := bound_le_helper m 1097 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1098 ≤ m := hm_gt
    have h1 : 603351 ≤ m*(m+1)/2 := bound_gt_helper m 1098 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_127 (m : ℕ) (hm1 : m ≥ 1) : my_pi (127*128) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 127*128 = 16256 := by decide
  rw [hk_eq]
  have hk : my_pi (16256) = 1889 := pi_16256
  have hm0 : my_pi (601156) = 49185 := pi_601156
  have hm1_val : my_pi (602253) = 49268 := pi_602253
  rcases le_or_gt m 1096 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 601156 := bound_le_helper m 1096 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1097 ≤ m := hm_gt
    have h1 : 602253 ≤ m*(m+1)/2 := bound_gt_helper m 1097 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_128 (m : ℕ) (hm1 : m ≥ 1) : my_pi (128*129) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 128*129 = 16512 := by decide
  rw [hk_eq]
  have hk : my_pi (16512) = 1912 := pi_16512
  have hm0 : my_pi (601156) = 49185 := pi_601156
  have hm1_val : my_pi (602253) = 49268 := pi_602253
  rcases le_or_gt m 1096 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 601156 := bound_le_helper m 1096 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1097 ≤ m := hm_gt
    have h1 : 602253 ≤ m*(m+1)/2 := bound_gt_helper m 1097 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_129 (m : ℕ) (hm1 : m ≥ 1) : my_pi (129*130) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 129*130 = 16770 := by decide
  rw [hk_eq]
  have hk : my_pi (16770) = 1938 := pi_16770
  have hm0 : my_pi (601156) = 49185 := pi_601156
  have hm1_val : my_pi (602253) = 49268 := pi_602253
  rcases le_or_gt m 1096 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 601156 := bound_le_helper m 1096 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1097 ≤ m := hm_gt
    have h1 : 602253 ≤ m*(m+1)/2 := bound_gt_helper m 1097 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_130 (m : ℕ) (hm1 : m ≥ 1) : my_pi (130*131) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 130*131 = 17030 := by decide
  rw [hk_eq]
  have hk : my_pi (17030) = 1964 := pi_17030
  have hm0 : my_pi (601156) = 49185 := pi_601156
  have hm1_val : my_pi (602253) = 49268 := pi_602253
  rcases le_or_gt m 1096 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 601156 := bound_le_helper m 1096 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1097 ≤ m := hm_gt
    have h1 : 602253 ≤ m*(m+1)/2 := bound_gt_helper m 1097 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_131 (m : ℕ) (hm1 : m ≥ 1) : my_pi (131*132) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 131*132 = 17292 := by decide
  rw [hk_eq]
  have hk : my_pi (17292) = 1987 := pi_17292
  have hm0 : my_pi (600060) = 49101 := pi_600060
  have hm1_val : my_pi (601156) = 49185 := pi_601156
  rcases le_or_gt m 1095 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 600060 := bound_le_helper m 1095 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1096 ≤ m := hm_gt
    have h1 : 601156 ≤ m*(m+1)/2 := bound_gt_helper m 1096 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_132 (m : ℕ) (hm1 : m ≥ 1) : my_pi (132*133) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 132*133 = 17556 := by decide
  rw [hk_eq]
  have hk : my_pi (17556) = 2018 := pi_17556
  have hm0 : my_pi (600060) = 49101 := pi_600060
  have hm1_val : my_pi (601156) = 49185 := pi_601156
  rcases le_or_gt m 1095 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 600060 := bound_le_helper m 1095 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1096 ≤ m := hm_gt
    have h1 : 601156 ≤ m*(m+1)/2 := bound_gt_helper m 1096 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_133 (m : ℕ) (hm1 : m ≥ 1) : my_pi (133*134) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 133*134 = 17822 := by decide
  rw [hk_eq]
  have hk : my_pi (17822) = 2043 := pi_17822
  have hm0 : my_pi (600060) = 49101 := pi_600060
  have hm1_val : my_pi (601156) = 49185 := pi_601156
  rcases le_or_gt m 1095 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 600060 := bound_le_helper m 1095 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1096 ≤ m := hm_gt
    have h1 : 601156 ≤ m*(m+1)/2 := bound_gt_helper m 1096 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_134 (m : ℕ) (hm1 : m ≥ 1) : my_pi (134*135) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 134*135 = 18090 := by decide
  rw [hk_eq]
  have hk : my_pi (18090) = 2073 := pi_18090
  have hm0 : my_pi (598965) = 49020 := pi_598965
  have hm1_val : my_pi (600060) = 49101 := pi_600060
  rcases le_or_gt m 1094 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 598965 := bound_le_helper m 1094 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1095 ≤ m := hm_gt
    have h1 : 600060 ≤ m*(m+1)/2 := bound_gt_helper m 1095 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_135 (m : ℕ) (hm1 : m ≥ 1) : my_pi (135*136) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 135*136 = 18360 := by decide
  rw [hk_eq]
  have hk : my_pi (18360) = 2103 := pi_18360
  have hm0 : my_pi (598965) = 49020 := pi_598965
  have hm1_val : my_pi (600060) = 49101 := pi_600060
  rcases le_or_gt m 1094 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 598965 := bound_le_helper m 1094 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1095 ≤ m := hm_gt
    have h1 : 600060 ≤ m*(m+1)/2 := bound_gt_helper m 1095 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_136 (m : ℕ) (hm1 : m ≥ 1) : my_pi (136*137) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 136*137 = 18632 := by decide
  rw [hk_eq]
  have hk : my_pi (18632) = 2129 := pi_18632
  have hm0 : my_pi (598965) = 49020 := pi_598965
  have hm1_val : my_pi (600060) = 49101 := pi_600060
  rcases le_or_gt m 1094 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 598965 := bound_le_helper m 1094 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1095 ≤ m := hm_gt
    have h1 : 600060 ≤ m*(m+1)/2 := bound_gt_helper m 1095 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_137 (m : ℕ) (hm1 : m ≥ 1) : my_pi (137*138) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 137*138 = 18906 := by decide
  rw [hk_eq]
  have hk : my_pi (18906) = 2150 := pi_18906
  have hm0 : my_pi (597871) = 48946 := pi_597871
  have hm1_val : my_pi (598965) = 49020 := pi_598965
  rcases le_or_gt m 1093 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 597871 := bound_le_helper m 1093 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1094 ≤ m := hm_gt
    have h1 : 598965 ≤ m*(m+1)/2 := bound_gt_helper m 1094 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_138 (m : ℕ) (hm1 : m ≥ 1) : my_pi (138*139) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 138*139 = 19182 := by decide
  rw [hk_eq]
  have hk : my_pi (19182) = 2175 := pi_19182
  have hm0 : my_pi (597871) = 48946 := pi_597871
  have hm1_val : my_pi (598965) = 49020 := pi_598965
  rcases le_or_gt m 1093 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 597871 := bound_le_helper m 1093 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1094 ≤ m := hm_gt
    have h1 : 598965 ≤ m*(m+1)/2 := bound_gt_helper m 1094 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_139 (m : ℕ) (hm1 : m ≥ 1) : my_pi (139*140) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 139*140 = 19460 := by decide
  rw [hk_eq]
  have hk : my_pi (19460) = 2206 := pi_19460
  have hm0 : my_pi (597871) = 48946 := pi_597871
  have hm1_val : my_pi (598965) = 49020 := pi_598965
  rcases le_or_gt m 1093 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 597871 := bound_le_helper m 1093 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1094 ≤ m := hm_gt
    have h1 : 598965 ≤ m*(m+1)/2 := bound_gt_helper m 1094 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_140 (m : ℕ) (hm1 : m ≥ 1) : my_pi (140*141) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 140*141 = 19740 := by decide
  rw [hk_eq]
  have hk : my_pi (19740) = 2234 := pi_19740
  have hm0 : my_pi (596778) = 48859 := pi_596778
  have hm1_val : my_pi (597871) = 48946 := pi_597871
  rcases le_or_gt m 1092 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 596778 := bound_le_helper m 1092 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1093 ≤ m := hm_gt
    have h1 : 597871 ≤ m*(m+1)/2 := bound_gt_helper m 1093 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_141 (m : ℕ) (hm1 : m ≥ 1) : my_pi (141*142) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 141*142 = 20022 := by decide
  rw [hk_eq]
  have hk : my_pi (20022) = 2264 := pi_20022
  have hm0 : my_pi (596778) = 48859 := pi_596778
  have hm1_val : my_pi (597871) = 48946 := pi_597871
  rcases le_or_gt m 1092 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 596778 := bound_le_helper m 1092 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1093 ≤ m := hm_gt
    have h1 : 597871 ≤ m*(m+1)/2 := bound_gt_helper m 1093 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_142 (m : ℕ) (hm1 : m ≥ 1) : my_pi (142*143) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 142*143 = 20306 := by decide
  rw [hk_eq]
  have hk : my_pi (20306) = 2293 := pi_20306
  have hm0 : my_pi (596778) = 48859 := pi_596778
  have hm1_val : my_pi (597871) = 48946 := pi_597871
  rcases le_or_gt m 1092 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 596778 := bound_le_helper m 1092 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1093 ≤ m := hm_gt
    have h1 : 597871 ≤ m*(m+1)/2 := bound_gt_helper m 1093 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_143 (m : ℕ) (hm1 : m ≥ 1) : my_pi (143*144) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 143*144 = 20592 := by decide
  rw [hk_eq]
  have hk : my_pi (20592) = 2321 := pi_20592
  have hm0 : my_pi (595686) = 48778 := pi_595686
  have hm1_val : my_pi (596778) = 48859 := pi_596778
  rcases le_or_gt m 1091 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 595686 := bound_le_helper m 1091 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1092 ≤ m := hm_gt
    have h1 : 596778 ≤ m*(m+1)/2 := bound_gt_helper m 1092 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_144 (m : ℕ) (hm1 : m ≥ 1) : my_pi (144*145) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 144*145 = 20880 := by decide
  rw [hk_eq]
  have hk : my_pi (20880) = 2348 := pi_20880
  have hm0 : my_pi (595686) = 48778 := pi_595686
  have hm1_val : my_pi (596778) = 48859 := pi_596778
  rcases le_or_gt m 1091 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 595686 := bound_le_helper m 1091 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1092 ≤ m := hm_gt
    have h1 : 596778 ≤ m*(m+1)/2 := bound_gt_helper m 1092 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_145 (m : ℕ) (hm1 : m ≥ 1) : my_pi (145*146) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 145*146 = 21170 := by decide
  rw [hk_eq]
  have hk : my_pi (21170) = 2380 := pi_21170
  have hm0 : my_pi (594595) = 48694 := pi_594595
  have hm1_val : my_pi (595686) = 48778 := pi_595686
  rcases le_or_gt m 1090 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 594595 := bound_le_helper m 1090 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1091 ≤ m := hm_gt
    have h1 : 595686 ≤ m*(m+1)/2 := bound_gt_helper m 1091 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_146 (m : ℕ) (hm1 : m ≥ 1) : my_pi (146*147) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 146*147 = 21462 := by decide
  rw [hk_eq]
  have hk : my_pi (21462) = 2406 := pi_21462
  have hm0 : my_pi (594595) = 48694 := pi_594595
  have hm1_val : my_pi (595686) = 48778 := pi_595686
  rcases le_or_gt m 1090 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 594595 := bound_le_helper m 1090 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1091 ≤ m := hm_gt
    have h1 : 595686 ≤ m*(m+1)/2 := bound_gt_helper m 1091 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_147 (m : ℕ) (hm1 : m ≥ 1) : my_pi (147*148) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 147*148 = 21756 := by decide
  rw [hk_eq]
  have hk : my_pi (21756) = 2440 := pi_21756
  have hm0 : my_pi (594595) = 48694 := pi_594595
  have hm1_val : my_pi (595686) = 48778 := pi_595686
  rcases le_or_gt m 1090 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 594595 := bound_le_helper m 1090 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1091 ≤ m := hm_gt
    have h1 : 595686 ≤ m*(m+1)/2 := bound_gt_helper m 1091 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_148 (m : ℕ) (hm1 : m ≥ 1) : my_pi (148*149) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 148*149 = 22052 := by decide
  rw [hk_eq]
  have hk : my_pi (22052) = 2471 := pi_22052
  have hm0 : my_pi (593505) = 48613 := pi_593505
  have hm1_val : my_pi (594595) = 48694 := pi_594595
  rcases le_or_gt m 1089 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 593505 := bound_le_helper m 1089 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1090 ≤ m := hm_gt
    have h1 : 594595 ≤ m*(m+1)/2 := bound_gt_helper m 1090 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_149 (m : ℕ) (hm1 : m ≥ 1) : my_pi (149*150) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 149*150 = 22350 := by decide
  rw [hk_eq]
  have hk : my_pi (22350) = 2502 := pi_22350
  have hm0 : my_pi (593505) = 48613 := pi_593505
  have hm1_val : my_pi (594595) = 48694 := pi_594595
  rcases le_or_gt m 1089 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 593505 := bound_le_helper m 1089 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1090 ≤ m := hm_gt
    have h1 : 594595 ≤ m*(m+1)/2 := bound_gt_helper m 1090 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_150 (m : ℕ) (hm1 : m ≥ 1) : my_pi (150*151) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 150*151 = 22650 := by decide
  rw [hk_eq]
  have hk : my_pi (22650) = 2530 := pi_22650
  have hm0 : my_pi (593505) = 48613 := pi_593505
  have hm1_val : my_pi (594595) = 48694 := pi_594595
  rcases le_or_gt m 1089 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 593505 := bound_le_helper m 1089 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1090 ≤ m := hm_gt
    have h1 : 594595 ≤ m*(m+1)/2 := bound_gt_helper m 1090 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_151 (m : ℕ) (hm1 : m ≥ 1) : my_pi (151*152) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 151*152 = 22952 := by decide
  rw [hk_eq]
  have hk : my_pi (22952) = 2560 := pi_22952
  have hm0 : my_pi (592416) = 48522 := pi_592416
  have hm1_val : my_pi (593505) = 48613 := pi_593505
  rcases le_or_gt m 1088 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 592416 := bound_le_helper m 1088 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1089 ≤ m := hm_gt
    have h1 : 593505 ≤ m*(m+1)/2 := bound_gt_helper m 1089 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_152 (m : ℕ) (hm1 : m ≥ 1) : my_pi (152*153) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 152*153 = 23256 := by decide
  rw [hk_eq]
  have hk : my_pi (23256) = 2593 := pi_23256
  have hm0 : my_pi (592416) = 48522 := pi_592416
  have hm1_val : my_pi (593505) = 48613 := pi_593505
  rcases le_or_gt m 1088 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 592416 := bound_le_helper m 1088 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1089 ≤ m := hm_gt
    have h1 : 593505 ≤ m*(m+1)/2 := bound_gt_helper m 1089 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_153 (m : ℕ) (hm1 : m ≥ 1) : my_pi (153*154) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 153*154 = 23562 := by decide
  rw [hk_eq]
  have hk : my_pi (23562) = 2620 := pi_23562
  have hm0 : my_pi (592416) = 48522 := pi_592416
  have hm1_val : my_pi (593505) = 48613 := pi_593505
  rcases le_or_gt m 1088 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 592416 := bound_le_helper m 1088 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1089 ≤ m := hm_gt
    have h1 : 593505 ≤ m*(m+1)/2 := bound_gt_helper m 1089 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_154 (m : ℕ) (hm1 : m ≥ 1) : my_pi (154*155) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 154*155 = 23870 := by decide
  rw [hk_eq]
  have hk : my_pi (23870) = 2654 := pi_23870
  have hm0 : my_pi (591328) = 48445 := pi_591328
  have hm1_val : my_pi (592416) = 48522 := pi_592416
  rcases le_or_gt m 1087 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 591328 := bound_le_helper m 1087 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1088 ≤ m := hm_gt
    have h1 : 592416 ≤ m*(m+1)/2 := bound_gt_helper m 1088 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_155 (m : ℕ) (hm1 : m ≥ 1) : my_pi (155*156) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 155*156 = 24180 := by decide
  rw [hk_eq]
  have hk : my_pi (24180) = 2691 := pi_24180
  have hm0 : my_pi (591328) = 48445 := pi_591328
  have hm1_val : my_pi (592416) = 48522 := pi_592416
  rcases le_or_gt m 1087 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 591328 := bound_le_helper m 1087 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1088 ≤ m := hm_gt
    have h1 : 592416 ≤ m*(m+1)/2 := bound_gt_helper m 1088 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_156 (m : ℕ) (hm1 : m ≥ 1) : my_pi (156*157) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 156*157 = 24492 := by decide
  rw [hk_eq]
  have hk : my_pi (24492) = 2717 := pi_24492
  have hm0 : my_pi (590241) = 48368 := pi_590241
  have hm1_val : my_pi (591328) = 48445 := pi_591328
  rcases le_or_gt m 1086 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 590241 := bound_le_helper m 1086 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1087 ≤ m := hm_gt
    have h1 : 591328 ≤ m*(m+1)/2 := bound_gt_helper m 1087 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_157 (m : ℕ) (hm1 : m ≥ 1) : my_pi (157*158) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 157*158 = 24806 := by decide
  rw [hk_eq]
  have hk : my_pi (24806) = 2743 := pi_24806
  have hm0 : my_pi (590241) = 48368 := pi_590241
  have hm1_val : my_pi (591328) = 48445 := pi_591328
  rcases le_or_gt m 1086 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 590241 := bound_le_helper m 1086 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1087 ≤ m := hm_gt
    have h1 : 591328 ≤ m*(m+1)/2 := bound_gt_helper m 1087 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_158 (m : ℕ) (hm1 : m ≥ 1) : my_pi (158*159) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 158*159 = 25122 := by decide
  rw [hk_eq]
  have hk : my_pi (25122) = 2773 := pi_25122
  have hm0 : my_pi (590241) = 48368 := pi_590241
  have hm1_val : my_pi (591328) = 48445 := pi_591328
  rcases le_or_gt m 1086 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 590241 := bound_le_helper m 1086 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1087 ≤ m := hm_gt
    have h1 : 591328 ≤ m*(m+1)/2 := bound_gt_helper m 1087 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_159 (m : ℕ) (hm1 : m ≥ 1) : my_pi (159*160) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 159*160 = 25440 := by decide
  rw [hk_eq]
  have hk : my_pi (25440) = 2804 := pi_25440
  have hm0 : my_pi (589155) = 48291 := pi_589155
  have hm1_val : my_pi (590241) = 48368 := pi_590241
  rcases le_or_gt m 1085 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 589155 := bound_le_helper m 1085 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1086 ≤ m := hm_gt
    have h1 : 590241 ≤ m*(m+1)/2 := bound_gt_helper m 1086 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_160 (m : ℕ) (hm1 : m ≥ 1) : my_pi (160*161) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 160*161 = 25760 := by decide
  rw [hk_eq]
  have hk : my_pi (25760) = 2836 := pi_25760
  have hm0 : my_pi (589155) = 48291 := pi_589155
  have hm1_val : my_pi (590241) = 48368 := pi_590241
  rcases le_or_gt m 1085 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 589155 := bound_le_helper m 1085 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1086 ≤ m := hm_gt
    have h1 : 590241 ≤ m*(m+1)/2 := bound_gt_helper m 1086 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_161 (m : ℕ) (hm1 : m ≥ 1) : my_pi (161*162) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 161*162 = 26082 := by decide
  rw [hk_eq]
  have hk : my_pi (26082) = 2866 := pi_26082
  have hm0 : my_pi (588070) = 48215 := pi_588070
  have hm1_val : my_pi (589155) = 48291 := pi_589155
  rcases le_or_gt m 1084 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 588070 := bound_le_helper m 1084 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1085 ≤ m := hm_gt
    have h1 : 589155 ≤ m*(m+1)/2 := bound_gt_helper m 1085 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_162 (m : ℕ) (hm1 : m ≥ 1) : my_pi (162*163) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 162*163 = 26406 := by decide
  rw [hk_eq]
  have hk : my_pi (26406) = 2900 := pi_26406
  have hm0 : my_pi (588070) = 48215 := pi_588070
  have hm1_val : my_pi (589155) = 48291 := pi_589155
  rcases le_or_gt m 1084 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 588070 := bound_le_helper m 1084 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1085 ≤ m := hm_gt
    have h1 : 589155 ≤ m*(m+1)/2 := bound_gt_helper m 1085 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_163 (m : ℕ) (hm1 : m ≥ 1) : my_pi (163*164) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 163*164 = 26732 := by decide
  rw [hk_eq]
  have hk : my_pi (26732) = 2935 := pi_26732
  have hm0 : my_pi (588070) = 48215 := pi_588070
  have hm1_val : my_pi (589155) = 48291 := pi_589155
  rcases le_or_gt m 1084 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 588070 := bound_le_helper m 1084 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1085 ≤ m := hm_gt
    have h1 : 589155 ≤ m*(m+1)/2 := bound_gt_helper m 1085 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_164 (m : ℕ) (hm1 : m ≥ 1) : my_pi (164*165) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 164*165 = 27060 := by decide
  rw [hk_eq]
  have hk : my_pi (27060) = 2966 := pi_27060
  have hm0 : my_pi (586986) = 48123 := pi_586986
  have hm1_val : my_pi (588070) = 48215 := pi_588070
  rcases le_or_gt m 1083 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 586986 := bound_le_helper m 1083 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1084 ≤ m := hm_gt
    have h1 : 588070 ≤ m*(m+1)/2 := bound_gt_helper m 1084 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_165 (m : ℕ) (hm1 : m ≥ 1) : my_pi (165*166) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 165*166 = 27390 := by decide
  rw [hk_eq]
  have hk : my_pi (27390) = 2993 := pi_27390
  have hm0 : my_pi (586986) = 48123 := pi_586986
  have hm1_val : my_pi (588070) = 48215 := pi_588070
  rcases le_or_gt m 1083 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 586986 := bound_le_helper m 1083 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1084 ≤ m := hm_gt
    have h1 : 588070 ≤ m*(m+1)/2 := bound_gt_helper m 1084 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_166 (m : ℕ) (hm1 : m ≥ 1) : my_pi (166*167) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 166*167 = 27722 := by decide
  rw [hk_eq]
  have hk : my_pi (27722) = 3022 := pi_27722
  have hm0 : my_pi (586986) = 48123 := pi_586986
  have hm1_val : my_pi (588070) = 48215 := pi_588070
  rcases le_or_gt m 1083 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 586986 := bound_le_helper m 1083 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1084 ≤ m := hm_gt
    have h1 : 588070 ≤ m*(m+1)/2 := bound_gt_helper m 1084 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_167 (m : ℕ) (hm1 : m ≥ 1) : my_pi (167*168) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 167*168 = 28056 := by decide
  rw [hk_eq]
  have hk : my_pi (28056) = 3060 := pi_28056
  have hm0 : my_pi (585903) = 48037 := pi_585903
  have hm1_val : my_pi (586986) = 48123 := pi_586986
  rcases le_or_gt m 1082 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 585903 := bound_le_helper m 1082 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1083 ≤ m := hm_gt
    have h1 : 586986 ≤ m*(m+1)/2 := bound_gt_helper m 1083 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_168 (m : ℕ) (hm1 : m ≥ 1) : my_pi (168*169) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 168*169 = 28392 := by decide
  rw [hk_eq]
  have hk : my_pi (28392) = 3088 := pi_28392
  have hm0 : my_pi (585903) = 48037 := pi_585903
  have hm1_val : my_pi (586986) = 48123 := pi_586986
  rcases le_or_gt m 1082 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 585903 := bound_le_helper m 1082 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1083 ≤ m := hm_gt
    have h1 : 586986 ≤ m*(m+1)/2 := bound_gt_helper m 1083 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_169 (m : ℕ) (hm1 : m ≥ 1) : my_pi (169*170) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 169*170 = 28730 := by decide
  rw [hk_eq]
  have hk : my_pi (28730) = 3130 := pi_28730
  have hm0 : my_pi (584821) = 47948 := pi_584821
  have hm1_val : my_pi (585903) = 48037 := pi_585903
  rcases le_or_gt m 1081 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 584821 := bound_le_helper m 1081 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1082 ≤ m := hm_gt
    have h1 : 585903 ≤ m*(m+1)/2 := bound_gt_helper m 1082 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_170 (m : ℕ) (hm1 : m ≥ 1) : my_pi (170*171) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 170*171 = 29070 := by decide
  rw [hk_eq]
  have hk : my_pi (29070) = 3161 := pi_29070
  have hm0 : my_pi (584821) = 47948 := pi_584821
  have hm1_val : my_pi (585903) = 48037 := pi_585903
  rcases le_or_gt m 1081 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 584821 := bound_le_helper m 1081 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1082 ≤ m := hm_gt
    have h1 : 585903 ≤ m*(m+1)/2 := bound_gt_helper m 1082 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_171 (m : ℕ) (hm1 : m ≥ 1) : my_pi (171*172) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 171*172 = 29412 := by decide
  rw [hk_eq]
  have hk : my_pi (29412) = 3196 := pi_29412
  have hm0 : my_pi (584821) = 47948 := pi_584821
  have hm1_val : my_pi (585903) = 48037 := pi_585903
  rcases le_or_gt m 1081 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 584821 := bound_le_helper m 1081 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1082 ≤ m := hm_gt
    have h1 : 585903 ≤ m*(m+1)/2 := bound_gt_helper m 1082 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_172 (m : ℕ) (hm1 : m ≥ 1) : my_pi (172*173) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 172*173 = 29756 := by decide
  rw [hk_eq]
  have hk : my_pi (29756) = 3225 := pi_29756
  have hm0 : my_pi (583740) = 47872 := pi_583740
  have hm1_val : my_pi (584821) = 47948 := pi_584821
  rcases le_or_gt m 1080 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 583740 := bound_le_helper m 1080 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1081 ≤ m := hm_gt
    have h1 : 584821 ≤ m*(m+1)/2 := bound_gt_helper m 1081 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_173 (m : ℕ) (hm1 : m ≥ 1) : my_pi (173*174) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 173*174 = 30102 := by decide
  rw [hk_eq]
  have hk : my_pi (30102) = 3254 := pi_30102
  have hm0 : my_pi (583740) = 47872 := pi_583740
  have hm1_val : my_pi (584821) = 47948 := pi_584821
  rcases le_or_gt m 1080 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 583740 := bound_le_helper m 1080 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1081 ≤ m := hm_gt
    have h1 : 584821 ≤ m*(m+1)/2 := bound_gt_helper m 1081 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_174 (m : ℕ) (hm1 : m ≥ 1) : my_pi (174*175) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 174*175 = 30450 := by decide
  rw [hk_eq]
  have hk : my_pi (30450) = 3288 := pi_30450
  have hm0 : my_pi (582660) = 47785 := pi_582660
  have hm1_val : my_pi (583740) = 47872 := pi_583740
  rcases le_or_gt m 1079 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 582660 := bound_le_helper m 1079 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1080 ≤ m := hm_gt
    have h1 : 583740 ≤ m*(m+1)/2 := bound_gt_helper m 1080 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_175 (m : ℕ) (hm1 : m ≥ 1) : my_pi (175*176) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 175*176 = 30800 := by decide
  rw [hk_eq]
  have hk : my_pi (30800) = 3319 := pi_30800
  have hm0 : my_pi (582660) = 47785 := pi_582660
  have hm1_val : my_pi (583740) = 47872 := pi_583740
  rcases le_or_gt m 1079 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 582660 := bound_le_helper m 1079 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1080 ≤ m := hm_gt
    have h1 : 583740 ≤ m*(m+1)/2 := bound_gt_helper m 1080 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_176 (m : ℕ) (hm1 : m ≥ 1) : my_pi (176*177) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 176*177 = 31152 := by decide
  rw [hk_eq]
  have hk : my_pi (31152) = 3355 := pi_31152
  have hm0 : my_pi (582660) = 47785 := pi_582660
  have hm1_val : my_pi (583740) = 47872 := pi_583740
  rcases le_or_gt m 1079 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 582660 := bound_le_helper m 1079 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1080 ≤ m := hm_gt
    have h1 : 583740 ≤ m*(m+1)/2 := bound_gt_helper m 1080 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_177 (m : ℕ) (hm1 : m ≥ 1) : my_pi (177*178) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 177*178 = 31506 := by decide
  rw [hk_eq]
  have hk : my_pi (31506) = 3389 := pi_31506
  have hm0 : my_pi (581581) = 47708 := pi_581581
  have hm1_val : my_pi (582660) = 47785 := pi_582660
  rcases le_or_gt m 1078 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 581581 := bound_le_helper m 1078 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1079 ≤ m := hm_gt
    have h1 : 582660 ≤ m*(m+1)/2 := bound_gt_helper m 1079 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_178 (m : ℕ) (hm1 : m ≥ 1) : my_pi (178*179) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 178*179 = 31862 := by decide
  rw [hk_eq]
  have hk : my_pi (31862) = 3423 := pi_31862
  have hm0 : my_pi (581581) = 47708 := pi_581581
  have hm1_val : my_pi (582660) = 47785 := pi_582660
  rcases le_or_gt m 1078 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 581581 := bound_le_helper m 1078 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1079 ≤ m := hm_gt
    have h1 : 582660 ≤ m*(m+1)/2 := bound_gt_helper m 1079 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_179 (m : ℕ) (hm1 : m ≥ 1) : my_pi (179*180) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 179*180 = 32220 := by decide
  rw [hk_eq]
  have hk : my_pi (32220) = 3456 := pi_32220
  have hm0 : my_pi (580503) = 47620 := pi_580503
  have hm1_val : my_pi (581581) = 47708 := pi_581581
  rcases le_or_gt m 1077 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 580503 := bound_le_helper m 1077 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1078 ≤ m := hm_gt
    have h1 : 581581 ≤ m*(m+1)/2 := bound_gt_helper m 1078 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_180 (m : ℕ) (hm1 : m ≥ 1) : my_pi (180*181) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 180*181 = 32580 := by decide
  rw [hk_eq]
  have hk : my_pi (32580) = 3497 := pi_32580
  have hm0 : my_pi (580503) = 47620 := pi_580503
  have hm1_val : my_pi (581581) = 47708 := pi_581581
  rcases le_or_gt m 1077 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 580503 := bound_le_helper m 1077 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1078 ≤ m := hm_gt
    have h1 : 581581 ≤ m*(m+1)/2 := bound_gt_helper m 1078 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_181 (m : ℕ) (hm1 : m ≥ 1) : my_pi (181*182) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 181*182 = 32942 := by decide
  rw [hk_eq]
  have hk : my_pi (32942) = 3531 := pi_32942
  have hm0 : my_pi (580503) = 47620 := pi_580503
  have hm1_val : my_pi (581581) = 47708 := pi_581581
  rcases le_or_gt m 1077 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 580503 := bound_le_helper m 1077 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1078 ≤ m := hm_gt
    have h1 : 581581 ≤ m*(m+1)/2 := bound_gt_helper m 1078 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_182 (m : ℕ) (hm1 : m ≥ 1) : my_pi (182*183) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 182*183 = 33306 := by decide
  rw [hk_eq]
  have hk : my_pi (33306) = 3565 := pi_33306
  have hm0 : my_pi (579426) = 47538 := pi_579426
  have hm1_val : my_pi (580503) = 47620 := pi_580503
  rcases le_or_gt m 1076 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 579426 := bound_le_helper m 1076 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1077 ≤ m := hm_gt
    have h1 : 580503 ≤ m*(m+1)/2 := bound_gt_helper m 1077 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_183 (m : ℕ) (hm1 : m ≥ 1) : my_pi (183*184) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 183*184 = 33672 := by decide
  rw [hk_eq]
  have hk : my_pi (33672) = 3607 := pi_33672
  have hm0 : my_pi (579426) = 47538 := pi_579426
  have hm1_val : my_pi (580503) = 47620 := pi_580503
  rcases le_or_gt m 1076 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 579426 := bound_le_helper m 1076 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1077 ≤ m := hm_gt
    have h1 : 580503 ≤ m*(m+1)/2 := bound_gt_helper m 1077 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_184 (m : ℕ) (hm1 : m ≥ 1) : my_pi (184*185) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 184*185 = 34040 := by decide
  rw [hk_eq]
  have hk : my_pi (34040) = 3642 := pi_34040
  have hm0 : my_pi (578350) = 47458 := pi_578350
  have hm1_val : my_pi (579426) = 47538 := pi_579426
  rcases le_or_gt m 1075 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 578350 := bound_le_helper m 1075 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1076 ≤ m := hm_gt
    have h1 : 579426 ≤ m*(m+1)/2 := bound_gt_helper m 1076 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_185 (m : ℕ) (hm1 : m ≥ 1) : my_pi (185*186) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 185*186 = 34410 := by decide
  rw [hk_eq]
  have hk : my_pi (34410) = 3676 := pi_34410
  have hm0 : my_pi (578350) = 47458 := pi_578350
  have hm1_val : my_pi (579426) = 47538 := pi_579426
  rcases le_or_gt m 1075 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 578350 := bound_le_helper m 1075 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1076 ≤ m := hm_gt
    have h1 : 579426 ≤ m*(m+1)/2 := bound_gt_helper m 1076 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_186 (m : ℕ) (hm1 : m ≥ 1) : my_pi (186*187) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 186*187 = 34782 := by decide
  rw [hk_eq]
  have hk : my_pi (34782) = 3715 := pi_34782
  have hm0 : my_pi (577275) = 47379 := pi_577275
  have hm1_val : my_pi (578350) = 47458 := pi_578350
  rcases le_or_gt m 1074 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 577275 := bound_le_helper m 1074 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1075 ≤ m := hm_gt
    have h1 : 578350 ≤ m*(m+1)/2 := bound_gt_helper m 1075 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_187 (m : ℕ) (hm1 : m ≥ 1) : my_pi (187*188) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 187*188 = 35156 := by decide
  rw [hk_eq]
  have hk : my_pi (35156) = 3749 := pi_35156
  have hm0 : my_pi (577275) = 47379 := pi_577275
  have hm1_val : my_pi (578350) = 47458 := pi_578350
  rcases le_or_gt m 1074 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 577275 := bound_le_helper m 1074 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1075 ≤ m := hm_gt
    have h1 : 578350 ≤ m*(m+1)/2 := bound_gt_helper m 1075 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_188 (m : ℕ) (hm1 : m ≥ 1) : my_pi (188*189) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 188*189 = 35532 := by decide
  rw [hk_eq]
  have hk : my_pi (35532) = 3783 := pi_35532
  have hm0 : my_pi (576201) = 47296 := pi_576201
  have hm1_val : my_pi (577275) = 47379 := pi_577275
  rcases le_or_gt m 1073 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 576201 := bound_le_helper m 1073 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1074 ≤ m := hm_gt
    have h1 : 577275 ≤ m*(m+1)/2 := bound_gt_helper m 1074 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_189 (m : ℕ) (hm1 : m ≥ 1) : my_pi (189*190) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 189*190 = 35910 := by decide
  rw [hk_eq]
  have hk : my_pi (35910) = 3814 := pi_35910
  have hm0 : my_pi (576201) = 47296 := pi_576201
  have hm1_val : my_pi (577275) = 47379 := pi_577275
  rcases le_or_gt m 1073 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 576201 := bound_le_helper m 1073 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1074 ≤ m := hm_gt
    have h1 : 577275 ≤ m*(m+1)/2 := bound_gt_helper m 1074 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_190 (m : ℕ) (hm1 : m ≥ 1) : my_pi (190*191) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 190*191 = 36290 := by decide
  rw [hk_eq]
  have hk : my_pi (36290) = 3850 := pi_36290
  have hm0 : my_pi (576201) = 47296 := pi_576201
  have hm1_val : my_pi (577275) = 47379 := pi_577275
  rcases le_or_gt m 1073 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 576201 := bound_le_helper m 1073 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1074 ≤ m := hm_gt
    have h1 : 577275 ≤ m*(m+1)/2 := bound_gt_helper m 1074 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_191 (m : ℕ) (hm1 : m ≥ 1) : my_pi (191*192) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 191*192 = 36672 := by decide
  rw [hk_eq]
  have hk : my_pi (36672) = 3887 := pi_36672
  have hm0 : my_pi (575128) = 47212 := pi_575128
  have hm1_val : my_pi (576201) = 47296 := pi_576201
  rcases le_or_gt m 1072 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 575128 := bound_le_helper m 1072 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1073 ≤ m := hm_gt
    have h1 : 576201 ≤ m*(m+1)/2 := bound_gt_helper m 1073 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_192 (m : ℕ) (hm1 : m ≥ 1) : my_pi (192*193) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 192*193 = 37056 := by decide
  rw [hk_eq]
  have hk : my_pi (37056) = 3929 := pi_37056
  have hm0 : my_pi (575128) = 47212 := pi_575128
  have hm1_val : my_pi (576201) = 47296 := pi_576201
  rcases le_or_gt m 1072 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 575128 := bound_le_helper m 1072 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1073 ≤ m := hm_gt
    have h1 : 576201 ≤ m*(m+1)/2 := bound_gt_helper m 1073 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_193 (m : ℕ) (hm1 : m ≥ 1) : my_pi (193*194) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 193*194 = 37442 := by decide
  rw [hk_eq]
  have hk : my_pi (37442) = 3963 := pi_37442
  have hm0 : my_pi (574056) = 47137 := pi_574056
  have hm1_val : my_pi (575128) = 47212 := pi_575128
  rcases le_or_gt m 1071 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 574056 := bound_le_helper m 1071 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1072 ≤ m := hm_gt
    have h1 : 575128 ≤ m*(m+1)/2 := bound_gt_helper m 1072 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_194 (m : ℕ) (hm1 : m ≥ 1) : my_pi (194*195) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 194*195 = 37830 := by decide
  rw [hk_eq]
  have hk : my_pi (37830) = 4000 := pi_37830
  have hm0 : my_pi (574056) = 47137 := pi_574056
  have hm1_val : my_pi (575128) = 47212 := pi_575128
  rcases le_or_gt m 1071 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 574056 := bound_le_helper m 1071 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1072 ≤ m := hm_gt
    have h1 : 575128 ≤ m*(m+1)/2 := bound_gt_helper m 1072 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_195 (m : ℕ) (hm1 : m ≥ 1) : my_pi (195*196) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 195*196 = 38220 := by decide
  rw [hk_eq]
  have hk : my_pi (38220) = 4034 := pi_38220
  have hm0 : my_pi (572985) = 47060 := pi_572985
  have hm1_val : my_pi (574056) = 47137 := pi_574056
  rcases le_or_gt m 1070 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 572985 := bound_le_helper m 1070 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1071 ≤ m := hm_gt
    have h1 : 574056 ≤ m*(m+1)/2 := bound_gt_helper m 1071 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_196 (m : ℕ) (hm1 : m ≥ 1) : my_pi (196*197) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 196*197 = 38612 := by decide
  rw [hk_eq]
  have hk : my_pi (38612) = 4068 := pi_38612
  have hm0 : my_pi (572985) = 47060 := pi_572985
  have hm1_val : my_pi (574056) = 47137 := pi_574056
  rcases le_or_gt m 1070 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 572985 := bound_le_helper m 1070 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1071 ≤ m := hm_gt
    have h1 : 574056 ≤ m*(m+1)/2 := bound_gt_helper m 1071 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_197 (m : ℕ) (hm1 : m ≥ 1) : my_pi (197*198) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 197*198 = 39006 := by decide
  rw [hk_eq]
  have hk : my_pi (39006) = 4107 := pi_39006
  have hm0 : my_pi (571915) = 46972 := pi_571915
  have hm1_val : my_pi (572985) = 47060 := pi_572985
  rcases le_or_gt m 1069 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 571915 := bound_le_helper m 1069 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1070 ≤ m := hm_gt
    have h1 : 572985 ≤ m*(m+1)/2 := bound_gt_helper m 1070 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_198 (m : ℕ) (hm1 : m ≥ 1) : my_pi (198*199) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 198*199 = 39402 := by decide
  rw [hk_eq]
  have hk : my_pi (39402) = 4148 := pi_39402
  have hm0 : my_pi (571915) = 46972 := pi_571915
  have hm1_val : my_pi (572985) = 47060 := pi_572985
  rcases le_or_gt m 1069 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 571915 := bound_le_helper m 1069 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1070 ≤ m := hm_gt
    have h1 : 572985 ≤ m*(m+1)/2 := bound_gt_helper m 1070 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_199 (m : ℕ) (hm1 : m ≥ 1) : my_pi (199*200) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 199*200 = 39800 := by decide
  rw [hk_eq]
  have hk : my_pi (39800) = 4183 := pi_39800
  have hm0 : my_pi (571915) = 46972 := pi_571915
  have hm1_val : my_pi (572985) = 47060 := pi_572985
  rcases le_or_gt m 1069 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 571915 := bound_le_helper m 1069 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1070 ≤ m := hm_gt
    have h1 : 572985 ≤ m*(m+1)/2 := bound_gt_helper m 1070 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_200 (m : ℕ) (hm1 : m ≥ 1) : my_pi (200*201) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 200*201 = 40200 := by decide
  rw [hk_eq]
  have hk : my_pi (40200) = 4223 := pi_40200
  have hm0 : my_pi (570846) = 46891 := pi_570846
  have hm1_val : my_pi (571915) = 46972 := pi_571915
  rcases le_or_gt m 1068 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 570846 := bound_le_helper m 1068 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1069 ≤ m := hm_gt
    have h1 : 571915 ≤ m*(m+1)/2 := bound_gt_helper m 1069 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_201 (m : ℕ) (hm1 : m ≥ 1) : my_pi (201*202) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 201*202 = 40602 := by decide
  rw [hk_eq]
  have hk : my_pi (40602) = 4256 := pi_40602
  have hm0 : my_pi (570846) = 46891 := pi_570846
  have hm1_val : my_pi (571915) = 46972 := pi_571915
  rcases le_or_gt m 1068 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 570846 := bound_le_helper m 1068 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1069 ≤ m := hm_gt
    have h1 : 571915 ≤ m*(m+1)/2 := bound_gt_helper m 1069 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_202 (m : ℕ) (hm1 : m ≥ 1) : my_pi (202*203) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 202*203 = 41006 := by decide
  rw [hk_eq]
  have hk : my_pi (41006) = 4291 := pi_41006
  have hm0 : my_pi (569778) = 46801 := pi_569778
  have hm1_val : my_pi (570846) = 46891 := pi_570846
  rcases le_or_gt m 1067 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 569778 := bound_le_helper m 1067 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1068 ≤ m := hm_gt
    have h1 : 570846 ≤ m*(m+1)/2 := bound_gt_helper m 1068 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_203 (m : ℕ) (hm1 : m ≥ 1) : my_pi (203*204) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 203*204 = 41412 := by decide
  rw [hk_eq]
  have hk : my_pi (41412) = 4333 := pi_41412
  have hm0 : my_pi (569778) = 46801 := pi_569778
  have hm1_val : my_pi (570846) = 46891 := pi_570846
  rcases le_or_gt m 1067 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 569778 := bound_le_helper m 1067 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1068 ≤ m := hm_gt
    have h1 : 570846 ≤ m*(m+1)/2 := bound_gt_helper m 1068 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_204 (m : ℕ) (hm1 : m ≥ 1) : my_pi (204*205) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 204*205 = 41820 := by decide
  rw [hk_eq]
  have hk : my_pi (41820) = 4372 := pi_41820
  have hm0 : my_pi (568711) = 46720 := pi_568711
  have hm1_val : my_pi (569778) = 46801 := pi_569778
  rcases le_or_gt m 1066 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 568711 := bound_le_helper m 1066 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1067 ≤ m := hm_gt
    have h1 : 569778 ≤ m*(m+1)/2 := bound_gt_helper m 1067 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_205 (m : ℕ) (hm1 : m ≥ 1) : my_pi (205*206) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 205*206 = 42230 := by decide
  rw [hk_eq]
  have hk : my_pi (42230) = 4416 := pi_42230
  have hm0 : my_pi (568711) = 46720 := pi_568711
  have hm1_val : my_pi (569778) = 46801 := pi_569778
  rcases le_or_gt m 1066 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 568711 := bound_le_helper m 1066 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1067 ≤ m := hm_gt
    have h1 : 569778 ≤ m*(m+1)/2 := bound_gt_helper m 1067 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_206 (m : ℕ) (hm1 : m ≥ 1) : my_pi (206*207) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 206*207 = 42642 := by decide
  rw [hk_eq]
  have hk : my_pi (42642) = 4456 := pi_42642
  have hm0 : my_pi (567645) = 46636 := pi_567645
  have hm1_val : my_pi (568711) = 46720 := pi_568711
  rcases le_or_gt m 1065 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 567645 := bound_le_helper m 1065 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1066 ≤ m := hm_gt
    have h1 : 568711 ≤ m*(m+1)/2 := bound_gt_helper m 1066 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_207 (m : ℕ) (hm1 : m ≥ 1) : my_pi (207*208) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 207*208 = 43056 := by decide
  rw [hk_eq]
  have hk : my_pi (43056) = 4500 := pi_43056
  have hm0 : my_pi (567645) = 46636 := pi_567645
  have hm1_val : my_pi (568711) = 46720 := pi_568711
  rcases le_or_gt m 1065 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 567645 := bound_le_helper m 1065 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1066 ≤ m := hm_gt
    have h1 : 568711 ≤ m*(m+1)/2 := bound_gt_helper m 1066 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_208 (m : ℕ) (hm1 : m ≥ 1) : my_pi (208*209) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 208*209 = 43472 := by decide
  rw [hk_eq]
  have hk : my_pi (43472) = 4531 := pi_43472
  have hm0 : my_pi (566580) = 46566 := pi_566580
  have hm1_val : my_pi (567645) = 46636 := pi_567645
  rcases le_or_gt m 1064 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 566580 := bound_le_helper m 1064 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1065 ≤ m := hm_gt
    have h1 : 567645 ≤ m*(m+1)/2 := bound_gt_helper m 1065 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_209 (m : ℕ) (hm1 : m ≥ 1) : my_pi (209*210) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 209*210 = 43890 := by decide
  rw [hk_eq]
  have hk : my_pi (43890) = 4567 := pi_43890
  have hm0 : my_pi (566580) = 46566 := pi_566580
  have hm1_val : my_pi (567645) = 46636 := pi_567645
  rcases le_or_gt m 1064 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 566580 := bound_le_helper m 1064 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1065 ≤ m := hm_gt
    have h1 : 567645 ≤ m*(m+1)/2 := bound_gt_helper m 1065 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_210 (m : ℕ) (hm1 : m ≥ 1) : my_pi (210*211) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 210*211 = 44310 := by decide
  rw [hk_eq]
  have hk : my_pi (44310) = 4612 := pi_44310
  have hm0 : my_pi (565516) = 46489 := pi_565516
  have hm1_val : my_pi (566580) = 46566 := pi_566580
  rcases le_or_gt m 1063 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 565516 := bound_le_helper m 1063 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1064 ≤ m := hm_gt
    have h1 : 566580 ≤ m*(m+1)/2 := bound_gt_helper m 1064 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_211 (m : ℕ) (hm1 : m ≥ 1) : my_pi (211*212) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 211*212 = 44732 := by decide
  rw [hk_eq]
  have hk : my_pi (44732) = 4649 := pi_44732
  have hm0 : my_pi (565516) = 46489 := pi_565516
  have hm1_val : my_pi (566580) = 46566 := pi_566580
  rcases le_or_gt m 1063 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 565516 := bound_le_helper m 1063 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1064 ≤ m := hm_gt
    have h1 : 566580 ≤ m*(m+1)/2 := bound_gt_helper m 1064 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_212 (m : ℕ) (hm1 : m ≥ 1) : my_pi (212*213) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 212*213 = 45156 := by decide
  rw [hk_eq]
  have hk : my_pi (45156) = 4687 := pi_45156
  have hm0 : my_pi (564453) = 46409 := pi_564453
  have hm1_val : my_pi (565516) = 46489 := pi_565516
  rcases le_or_gt m 1062 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 564453 := bound_le_helper m 1062 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1063 ≤ m := hm_gt
    have h1 : 565516 ≤ m*(m+1)/2 := bound_gt_helper m 1063 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_213 (m : ℕ) (hm1 : m ≥ 1) : my_pi (213*214) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 213*214 = 45582 := by decide
  rw [hk_eq]
  have hk : my_pi (45582) = 4724 := pi_45582
  have hm0 : my_pi (564453) = 46409 := pi_564453
  have hm1_val : my_pi (565516) = 46489 := pi_565516
  rcases le_or_gt m 1062 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 564453 := bound_le_helper m 1062 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1063 ≤ m := hm_gt
    have h1 : 565516 ≤ m*(m+1)/2 := bound_gt_helper m 1063 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_214 (m : ℕ) (hm1 : m ≥ 1) : my_pi (214*215) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 214*215 = 46010 := by decide
  rw [hk_eq]
  have hk : my_pi (46010) = 4761 := pi_46010
  have hm0 : my_pi (563391) = 46329 := pi_563391
  have hm1_val : my_pi (564453) = 46409 := pi_564453
  rcases le_or_gt m 1061 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 563391 := bound_le_helper m 1061 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1062 ≤ m := hm_gt
    have h1 : 564453 ≤ m*(m+1)/2 := bound_gt_helper m 1062 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_215 (m : ℕ) (hm1 : m ≥ 1) : my_pi (215*216) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 215*216 = 46440 := by decide
  rw [hk_eq]
  have hk : my_pi (46440) = 4798 := pi_46440
  have hm0 : my_pi (563391) = 46329 := pi_563391
  have hm1_val : my_pi (564453) = 46409 := pi_564453
  rcases le_or_gt m 1061 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 563391 := bound_le_helper m 1061 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1062 ≤ m := hm_gt
    have h1 : 564453 ≤ m*(m+1)/2 := bound_gt_helper m 1062 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_216 (m : ℕ) (hm1 : m ≥ 1) : my_pi (216*217) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 216*217 = 46872 := by decide
  rw [hk_eq]
  have hk : my_pi (46872) = 4843 := pi_46872
  have hm0 : my_pi (562330) = 46241 := pi_562330
  have hm1_val : my_pi (563391) = 46329 := pi_563391
  rcases le_or_gt m 1060 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 562330 := bound_le_helper m 1060 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1061 ≤ m := hm_gt
    have h1 : 563391 ≤ m*(m+1)/2 := bound_gt_helper m 1061 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_217 (m : ℕ) (hm1 : m ≥ 1) : my_pi (217*218) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 217*218 = 47306 := by decide
  rw [hk_eq]
  have hk : my_pi (47306) = 4878 := pi_47306
  have hm0 : my_pi (562330) = 46241 := pi_562330
  have hm1_val : my_pi (563391) = 46329 := pi_563391
  rcases le_or_gt m 1060 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 562330 := bound_le_helper m 1060 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1061 ≤ m := hm_gt
    have h1 : 563391 ≤ m*(m+1)/2 := bound_gt_helper m 1061 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_218 (m : ℕ) (hm1 : m ≥ 1) : my_pi (218*219) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 218*219 = 47742 := by decide
  rw [hk_eq]
  have hk : my_pi (47742) = 4922 := pi_47742
  have hm0 : my_pi (561270) = 46177 := pi_561270
  have hm1_val : my_pi (562330) = 46241 := pi_562330
  rcases le_or_gt m 1059 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 561270 := bound_le_helper m 1059 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1060 ≤ m := hm_gt
    have h1 : 562330 ≤ m*(m+1)/2 := bound_gt_helper m 1060 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_219 (m : ℕ) (hm1 : m ≥ 1) : my_pi (219*220) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 219*220 = 48180 := by decide
  rw [hk_eq]
  have hk : my_pi (48180) = 4960 := pi_48180
  have hm0 : my_pi (561270) = 46177 := pi_561270
  have hm1_val : my_pi (562330) = 46241 := pi_562330
  rcases le_or_gt m 1059 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 561270 := bound_le_helper m 1059 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1060 ≤ m := hm_gt
    have h1 : 562330 ≤ m*(m+1)/2 := bound_gt_helper m 1060 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_220 (m : ℕ) (hm1 : m ≥ 1) : my_pi (220*221) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 220*221 = 48620 := by decide
  rw [hk_eq]
  have hk : my_pi (48620) = 5001 := pi_48620
  have hm0 : my_pi (560211) = 46093 := pi_560211
  have hm1_val : my_pi (561270) = 46177 := pi_561270
  rcases le_or_gt m 1058 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 560211 := bound_le_helper m 1058 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1059 ≤ m := hm_gt
    have h1 : 561270 ≤ m*(m+1)/2 := bound_gt_helper m 1059 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_221 (m : ℕ) (hm1 : m ≥ 1) : my_pi (221*222) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 221*222 = 49062 := by decide
  rw [hk_eq]
  have hk : my_pi (49062) = 5043 := pi_49062
  have hm0 : my_pi (560211) = 46093 := pi_560211
  have hm1_val : my_pi (561270) = 46177 := pi_561270
  rcases le_or_gt m 1058 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 560211 := bound_le_helper m 1058 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1059 ≤ m := hm_gt
    have h1 : 561270 ≤ m*(m+1)/2 := bound_gt_helper m 1059 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_222 (m : ℕ) (hm1 : m ≥ 1) : my_pi (222*223) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 222*223 = 49506 := by decide
  rw [hk_eq]
  have hk : my_pi (49506) = 5086 := pi_49506
  have hm0 : my_pi (559153) = 46004 := pi_559153
  have hm1_val : my_pi (560211) = 46093 := pi_560211
  rcases le_or_gt m 1057 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 559153 := bound_le_helper m 1057 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1058 ≤ m := hm_gt
    have h1 : 560211 ≤ m*(m+1)/2 := bound_gt_helper m 1058 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_223 (m : ℕ) (hm1 : m ≥ 1) : my_pi (223*224) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 223*224 = 49952 := by decide
  rw [hk_eq]
  have hk : my_pi (49952) = 5129 := pi_49952
  have hm0 : my_pi (559153) = 46004 := pi_559153
  have hm1_val : my_pi (560211) = 46093 := pi_560211
  rcases le_or_gt m 1057 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 559153 := bound_le_helper m 1057 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1058 ≤ m := hm_gt
    have h1 : 560211 ≤ m*(m+1)/2 := bound_gt_helper m 1058 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_224 (m : ℕ) (hm1 : m ≥ 1) : my_pi (224*225) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 224*225 = 50400 := by decide
  rw [hk_eq]
  have hk : my_pi (50400) = 5172 := pi_50400
  have hm0 : my_pi (558096) = 45928 := pi_558096
  have hm1_val : my_pi (559153) = 46004 := pi_559153
  rcases le_or_gt m 1056 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 558096 := bound_le_helper m 1056 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1057 ≤ m := hm_gt
    have h1 : 559153 ≤ m*(m+1)/2 := bound_gt_helper m 1057 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_225 (m : ℕ) (hm1 : m ≥ 1) : my_pi (225*226) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 225*226 = 50850 := by decide
  rw [hk_eq]
  have hk : my_pi (50850) = 5208 := pi_50850
  have hm0 : my_pi (558096) = 45928 := pi_558096
  have hm1_val : my_pi (559153) = 46004 := pi_559153
  rcases le_or_gt m 1056 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 558096 := bound_le_helper m 1056 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1057 ≤ m := hm_gt
    have h1 : 559153 ≤ m*(m+1)/2 := bound_gt_helper m 1057 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_226 (m : ℕ) (hm1 : m ≥ 1) : my_pi (226*227) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 226*227 = 51302 := by decide
  rw [hk_eq]
  have hk : my_pi (51302) = 5248 := pi_51302
  have hm0 : my_pi (557040) = 45857 := pi_557040
  have hm1_val : my_pi (558096) = 45928 := pi_558096
  rcases le_or_gt m 1055 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 557040 := bound_le_helper m 1055 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1056 ≤ m := hm_gt
    have h1 : 558096 ≤ m*(m+1)/2 := bound_gt_helper m 1056 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_227 (m : ℕ) (hm1 : m ≥ 1) : my_pi (227*228) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 227*228 = 51756 := by decide
  rw [hk_eq]
  have hk : my_pi (51756) = 5295 := pi_51756
  have hm0 : my_pi (557040) = 45857 := pi_557040
  have hm1_val : my_pi (558096) = 45928 := pi_558096
  rcases le_or_gt m 1055 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 557040 := bound_le_helper m 1055 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1056 ≤ m := hm_gt
    have h1 : 558096 ≤ m*(m+1)/2 := bound_gt_helper m 1056 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_228 (m : ℕ) (hm1 : m ≥ 1) : my_pi (228*229) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 228*229 = 52212 := by decide
  rw [hk_eq]
  have hk : my_pi (52212) = 5338 := pi_52212
  have hm0 : my_pi (555985) = 45765 := pi_555985
  have hm1_val : my_pi (557040) = 45857 := pi_557040
  rcases le_or_gt m 1054 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 555985 := bound_le_helper m 1054 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1055 ≤ m := hm_gt
    have h1 : 557040 ≤ m*(m+1)/2 := bound_gt_helper m 1055 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_229 (m : ℕ) (hm1 : m ≥ 1) : my_pi (229*230) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 229*230 = 52670 := by decide
  rw [hk_eq]
  have hk : my_pi (52670) = 5376 := pi_52670
  have hm0 : my_pi (555985) = 45765 := pi_555985
  have hm1_val : my_pi (557040) = 45857 := pi_557040
  rcases le_or_gt m 1054 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 555985 := bound_le_helper m 1054 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1055 ≤ m := hm_gt
    have h1 : 557040 ≤ m*(m+1)/2 := bound_gt_helper m 1055 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_230 (m : ℕ) (hm1 : m ≥ 1) : my_pi (230*231) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 230*231 = 53130 := by decide
  rw [hk_eq]
  have hk : my_pi (53130) = 5421 := pi_53130
  have hm0 : my_pi (554931) = 45700 := pi_554931
  have hm1_val : my_pi (555985) = 45765 := pi_555985
  rcases le_or_gt m 1053 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 554931 := bound_le_helper m 1053 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1054 ≤ m := hm_gt
    have h1 : 555985 ≤ m*(m+1)/2 := bound_gt_helper m 1054 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_231 (m : ℕ) (hm1 : m ≥ 1) : my_pi (231*232) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 231*232 = 53592 := by decide
  rw [hk_eq]
  have hk : my_pi (53592) = 5459 := pi_53592
  have hm0 : my_pi (553878) = 45618 := pi_553878
  have hm1_val : my_pi (554931) = 45700 := pi_554931
  rcases le_or_gt m 1052 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 553878 := bound_le_helper m 1052 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1053 ≤ m := hm_gt
    have h1 : 554931 ≤ m*(m+1)/2 := bound_gt_helper m 1053 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_232 (m : ℕ) (hm1 : m ≥ 1) : my_pi (232*233) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 232*233 = 54056 := by decide
  rw [hk_eq]
  have hk : my_pi (54056) = 5505 := pi_54056
  have hm0 : my_pi (553878) = 45618 := pi_553878
  have hm1_val : my_pi (554931) = 45700 := pi_554931
  rcases le_or_gt m 1052 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 553878 := bound_le_helper m 1052 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1053 ≤ m := hm_gt
    have h1 : 554931 ≤ m*(m+1)/2 := bound_gt_helper m 1053 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_233 (m : ℕ) (hm1 : m ≥ 1) : my_pi (233*234) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 233*234 = 54522 := by decide
  rw [hk_eq]
  have hk : my_pi (54522) = 5548 := pi_54522
  have hm0 : my_pi (552826) = 45535 := pi_552826
  have hm1_val : my_pi (553878) = 45618 := pi_553878
  rcases le_or_gt m 1051 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 552826 := bound_le_helper m 1051 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1052 ≤ m := hm_gt
    have h1 : 553878 ≤ m*(m+1)/2 := bound_gt_helper m 1052 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_234 (m : ℕ) (hm1 : m ≥ 1) : my_pi (234*235) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 234*235 = 54990 := by decide
  rw [hk_eq]
  have hk : my_pi (54990) = 5590 := pi_54990
  have hm0 : my_pi (552826) = 45535 := pi_552826
  have hm1_val : my_pi (553878) = 45618 := pi_553878
  rcases le_or_gt m 1051 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 552826 := bound_le_helper m 1051 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1052 ≤ m := hm_gt
    have h1 : 553878 ≤ m*(m+1)/2 := bound_gt_helper m 1052 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_235 (m : ℕ) (hm1 : m ≥ 1) : my_pi (235*236) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 235*236 = 55460 := by decide
  rw [hk_eq]
  have hk : my_pi (55460) = 5630 := pi_55460
  have hm0 : my_pi (551775) = 45461 := pi_551775
  have hm1_val : my_pi (552826) = 45535 := pi_552826
  rcases le_or_gt m 1050 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 551775 := bound_le_helper m 1050 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1051 ≤ m := hm_gt
    have h1 : 552826 ≤ m*(m+1)/2 := bound_gt_helper m 1051 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_236 (m : ℕ) (hm1 : m ≥ 1) : my_pi (236*237) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 236*237 = 55932 := by decide
  rw [hk_eq]
  have hk : my_pi (55932) = 5678 := pi_55932
  have hm0 : my_pi (551775) = 45461 := pi_551775
  have hm1_val : my_pi (552826) = 45535 := pi_552826
  rcases le_or_gt m 1050 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 551775 := bound_le_helper m 1050 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1051 ≤ m := hm_gt
    have h1 : 552826 ≤ m*(m+1)/2 := bound_gt_helper m 1051 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_237 (m : ℕ) (hm1 : m ≥ 1) : my_pi (237*238) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 237*238 = 56406 := by decide
  rw [hk_eq]
  have hk : my_pi (56406) = 5718 := pi_56406
  have hm0 : my_pi (550725) = 45379 := pi_550725
  have hm1_val : my_pi (551775) = 45461 := pi_551775
  rcases le_or_gt m 1049 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 550725 := bound_le_helper m 1049 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1050 ≤ m := hm_gt
    have h1 : 551775 ≤ m*(m+1)/2 := bound_gt_helper m 1050 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_238 (m : ℕ) (hm1 : m ≥ 1) : my_pi (238*239) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 238*239 = 56882 := by decide
  rw [hk_eq]
  have hk : my_pi (56882) = 5766 := pi_56882
  have hm0 : my_pi (550725) = 45379 := pi_550725
  have hm1_val : my_pi (551775) = 45461 := pi_551775
  rcases le_or_gt m 1049 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 550725 := bound_le_helper m 1049 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1050 ≤ m := hm_gt
    have h1 : 551775 ≤ m*(m+1)/2 := bound_gt_helper m 1050 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_239 (m : ℕ) (hm1 : m ≥ 1) : my_pi (239*240) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 239*240 = 57360 := by decide
  rw [hk_eq]
  have hk : my_pi (57360) = 5816 := pi_57360
  have hm0 : my_pi (549676) = 45298 := pi_549676
  have hm1_val : my_pi (550725) = 45379 := pi_550725
  rcases le_or_gt m 1048 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 549676 := bound_le_helper m 1048 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1049 ≤ m := hm_gt
    have h1 : 550725 ≤ m*(m+1)/2 := bound_gt_helper m 1049 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_240 (m : ℕ) (hm1 : m ≥ 1) : my_pi (240*241) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 240*241 = 57840 := by decide
  rw [hk_eq]
  have hk : my_pi (57840) = 5860 := pi_57840
  have hm0 : my_pi (548628) = 45214 := pi_548628
  have hm1_val : my_pi (549676) = 45298 := pi_549676
  rcases le_or_gt m 1047 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 548628 := bound_le_helper m 1047 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1048 ≤ m := hm_gt
    have h1 : 549676 ≤ m*(m+1)/2 := bound_gt_helper m 1048 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_241 (m : ℕ) (hm1 : m ≥ 1) : my_pi (241*242) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 241*242 = 58322 := by decide
  rw [hk_eq]
  have hk : my_pi (58322) = 5905 := pi_58322
  have hm0 : my_pi (548628) = 45214 := pi_548628
  have hm1_val : my_pi (549676) = 45298 := pi_549676
  rcases le_or_gt m 1047 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 548628 := bound_le_helper m 1047 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1048 ≤ m := hm_gt
    have h1 : 549676 ≤ m*(m+1)/2 := bound_gt_helper m 1048 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_242 (m : ℕ) (hm1 : m ≥ 1) : my_pi (242*243) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 242*243 = 58806 := by decide
  rw [hk_eq]
  have hk : my_pi (58806) = 5948 := pi_58806
  have hm0 : my_pi (547581) = 45136 := pi_547581
  have hm1_val : my_pi (548628) = 45214 := pi_548628
  rcases le_or_gt m 1046 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 547581 := bound_le_helper m 1046 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1047 ≤ m := hm_gt
    have h1 : 548628 ≤ m*(m+1)/2 := bound_gt_helper m 1047 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_243 (m : ℕ) (hm1 : m ≥ 1) : my_pi (243*244) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 243*244 = 59292 := by decide
  rw [hk_eq]
  have hk : my_pi (59292) = 5995 := pi_59292
  have hm0 : my_pi (547581) = 45136 := pi_547581
  have hm1_val : my_pi (548628) = 45214 := pi_548628
  rcases le_or_gt m 1046 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 547581 := bound_le_helper m 1046 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1047 ≤ m := hm_gt
    have h1 : 548628 ≤ m*(m+1)/2 := bound_gt_helper m 1047 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_244 (m : ℕ) (hm1 : m ≥ 1) : my_pi (244*245) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 244*245 = 59780 := by decide
  rw [hk_eq]
  have hk : my_pi (59780) = 6043 := pi_59780
  have hm0 : my_pi (546535) = 45058 := pi_546535
  have hm1_val : my_pi (547581) = 45136 := pi_547581
  rcases le_or_gt m 1045 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 546535 := bound_le_helper m 1045 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1046 ≤ m := hm_gt
    have h1 : 547581 ≤ m*(m+1)/2 := bound_gt_helper m 1046 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_245 (m : ℕ) (hm1 : m ≥ 1) : my_pi (245*246) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 245*246 = 60270 := by decide
  rw [hk_eq]
  have hk : my_pi (60270) = 6082 := pi_60270
  have hm0 : my_pi (546535) = 45058 := pi_546535
  have hm1_val : my_pi (547581) = 45136 := pi_547581
  rcases le_or_gt m 1045 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 546535 := bound_le_helper m 1045 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1046 ≤ m := hm_gt
    have h1 : 547581 ≤ m*(m+1)/2 := bound_gt_helper m 1046 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_246 (m : ℕ) (hm1 : m ≥ 1) : my_pi (246*247) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 246*247 = 60762 := by decide
  rw [hk_eq]
  have hk : my_pi (60762) = 6125 := pi_60762
  have hm0 : my_pi (545490) = 44980 := pi_545490
  have hm1_val : my_pi (546535) = 45058 := pi_546535
  rcases le_or_gt m 1044 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 545490 := bound_le_helper m 1044 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1045 ≤ m := hm_gt
    have h1 : 546535 ≤ m*(m+1)/2 := bound_gt_helper m 1045 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_247 (m : ℕ) (hm1 : m ≥ 1) : my_pi (247*248) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 247*248 = 61256 := by decide
  rw [hk_eq]
  have hk : my_pi (61256) = 6164 := pi_61256
  have hm0 : my_pi (545490) = 44980 := pi_545490
  have hm1_val : my_pi (546535) = 45058 := pi_546535
  rcases le_or_gt m 1044 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 545490 := bound_le_helper m 1044 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1045 ≤ m := hm_gt
    have h1 : 546535 ≤ m*(m+1)/2 := bound_gt_helper m 1045 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_248 (m : ℕ) (hm1 : m ≥ 1) : my_pi (248*249) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 248*249 = 61752 := by decide
  rw [hk_eq]
  have hk : my_pi (61752) = 6213 := pi_61752
  have hm0 : my_pi (544446) = 44908 := pi_544446
  have hm1_val : my_pi (545490) = 44980 := pi_545490
  rcases le_or_gt m 1043 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 544446 := bound_le_helper m 1043 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1044 ≤ m := hm_gt
    have h1 : 545490 ≤ m*(m+1)/2 := bound_gt_helper m 1044 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_249 (m : ℕ) (hm1 : m ≥ 1) : my_pi (249*250) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 249*250 = 62250 := by decide
  rw [hk_eq]
  have hk : my_pi (62250) = 6256 := pi_62250
  have hm0 : my_pi (543403) = 44835 := pi_543403
  have hm1_val : my_pi (544446) = 44908 := pi_544446
  rcases le_or_gt m 1042 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 543403 := bound_le_helper m 1042 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1043 ≤ m := hm_gt
    have h1 : 544446 ≤ m*(m+1)/2 := bound_gt_helper m 1043 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_250 (m : ℕ) (hm1 : m ≥ 1) : my_pi (250*251) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 250*251 = 62750 := by decide
  rw [hk_eq]
  have hk : my_pi (62750) = 6297 := pi_62750
  have hm0 : my_pi (543403) = 44835 := pi_543403
  have hm1_val : my_pi (544446) = 44908 := pi_544446
  rcases le_or_gt m 1042 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 543403 := bound_le_helper m 1042 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1043 ≤ m := hm_gt
    have h1 : 544446 ≤ m*(m+1)/2 := bound_gt_helper m 1043 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_251 (m : ℕ) (hm1 : m ≥ 1) : my_pi (251*252) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 251*252 = 63252 := by decide
  rw [hk_eq]
  have hk : my_pi (63252) = 6338 := pi_63252
  have hm0 : my_pi (542361) = 44753 := pi_542361
  have hm1_val : my_pi (543403) = 44835 := pi_543403
  rcases le_or_gt m 1041 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 542361 := bound_le_helper m 1041 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1042 ≤ m := hm_gt
    have h1 : 543403 ≤ m*(m+1)/2 := bound_gt_helper m 1042 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_252 (m : ℕ) (hm1 : m ≥ 1) : my_pi (252*253) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 252*253 = 63756 := by decide
  rw [hk_eq]
  have hk : my_pi (63756) = 6393 := pi_63756
  have hm0 : my_pi (542361) = 44753 := pi_542361
  have hm1_val : my_pi (543403) = 44835 := pi_543403
  rcases le_or_gt m 1041 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 542361 := bound_le_helper m 1041 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1042 ≤ m := hm_gt
    have h1 : 543403 ≤ m*(m+1)/2 := bound_gt_helper m 1042 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_253 (m : ℕ) (hm1 : m ≥ 1) : my_pi (253*254) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 253*254 = 64262 := by decide
  rw [hk_eq]
  have hk : my_pi (64262) = 6434 := pi_64262
  have hm0 : my_pi (541320) = 44668 := pi_541320
  have hm1_val : my_pi (542361) = 44753 := pi_542361
  rcases le_or_gt m 1040 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 541320 := bound_le_helper m 1040 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1041 ≤ m := hm_gt
    have h1 : 542361 ≤ m*(m+1)/2 := bound_gt_helper m 1041 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_254 (m : ℕ) (hm1 : m ≥ 1) : my_pi (254*255) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 254*255 = 64770 := by decide
  rw [hk_eq]
  have hk : my_pi (64770) = 6474 := pi_64770
  have hm0 : my_pi (541320) = 44668 := pi_541320
  have hm1_val : my_pi (542361) = 44753 := pi_542361
  rcases le_or_gt m 1040 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 541320 := bound_le_helper m 1040 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1041 ≤ m := hm_gt
    have h1 : 542361 ≤ m*(m+1)/2 := bound_gt_helper m 1041 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_255 (m : ℕ) (hm1 : m ≥ 1) : my_pi (255*256) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 255*256 = 65280 := by decide
  rw [hk_eq]
  have hk : my_pi (65280) = 6521 := pi_65280
  have hm0 : my_pi (540280) = 44592 := pi_540280
  have hm1_val : my_pi (541320) = 44668 := pi_541320
  rcases le_or_gt m 1039 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 540280 := bound_le_helper m 1039 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1040 ≤ m := hm_gt
    have h1 : 541320 ≤ m*(m+1)/2 := bound_gt_helper m 1040 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_256 (m : ℕ) (hm1 : m ≥ 1) : my_pi (256*257) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 256*257 = 65792 := by decide
  rw [hk_eq]
  have hk : my_pi (65792) = 6572 := pi_65792
  have hm0 : my_pi (539241) = 44521 := pi_539241
  have hm1_val : my_pi (540280) = 44592 := pi_540280
  rcases le_or_gt m 1038 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 539241 := bound_le_helper m 1038 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1039 ≤ m := hm_gt
    have h1 : 540280 ≤ m*(m+1)/2 := bound_gt_helper m 1039 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_257 (m : ℕ) (hm1 : m ≥ 1) : my_pi (257*258) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 257*258 = 66306 := by decide
  rw [hk_eq]
  have hk : my_pi (66306) = 6613 := pi_66306
  have hm0 : my_pi (539241) = 44521 := pi_539241
  have hm1_val : my_pi (540280) = 44592 := pi_540280
  rcases le_or_gt m 1038 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 539241 := bound_le_helper m 1038 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1039 ≤ m := hm_gt
    have h1 : 540280 ≤ m*(m+1)/2 := bound_gt_helper m 1039 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_258 (m : ℕ) (hm1 : m ≥ 1) : my_pi (258*259) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 258*259 = 66822 := by decide
  rw [hk_eq]
  have hk : my_pi (66822) = 6659 := pi_66822
  have hm0 : my_pi (538203) = 44441 := pi_538203
  have hm1_val : my_pi (539241) = 44521 := pi_539241
  rcases le_or_gt m 1037 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 538203 := bound_le_helper m 1037 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1038 ≤ m := hm_gt
    have h1 : 539241 ≤ m*(m+1)/2 := bound_gt_helper m 1038 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_259 (m : ℕ) (hm1 : m ≥ 1) : my_pi (259*260) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 259*260 = 67340 := by decide
  rw [hk_eq]
  have hk : my_pi (67340) = 6707 := pi_67340
  have hm0 : my_pi (538203) = 44441 := pi_538203
  have hm1_val : my_pi (539241) = 44521 := pi_539241
  rcases le_or_gt m 1037 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 538203 := bound_le_helper m 1037 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1038 ≤ m := hm_gt
    have h1 : 539241 ≤ m*(m+1)/2 := bound_gt_helper m 1038 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_260 (m : ℕ) (hm1 : m ≥ 1) : my_pi (260*261) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 260*261 = 67860 := by decide
  rw [hk_eq]
  have hk : my_pi (67860) = 6759 := pi_67860
  have hm0 : my_pi (537166) = 44371 := pi_537166
  have hm1_val : my_pi (538203) = 44441 := pi_538203
  rcases le_or_gt m 1036 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 537166 := bound_le_helper m 1036 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1037 ≤ m := hm_gt
    have h1 : 538203 ≤ m*(m+1)/2 := bound_gt_helper m 1037 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_261 (m : ℕ) (hm1 : m ≥ 1) : my_pi (261*262) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 261*262 = 68382 := by decide
  rw [hk_eq]
  have hk : my_pi (68382) = 6800 := pi_68382
  have hm0 : my_pi (536130) = 44279 := pi_536130
  have hm1_val : my_pi (537166) = 44371 := pi_537166
  rcases le_or_gt m 1035 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 536130 := bound_le_helper m 1035 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1036 ≤ m := hm_gt
    have h1 : 537166 ≤ m*(m+1)/2 := bound_gt_helper m 1036 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_262 (m : ℕ) (hm1 : m ≥ 1) : my_pi (262*263) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 262*263 = 68906 := by decide
  rw [hk_eq]
  have hk : my_pi (68906) = 6848 := pi_68906
  have hm0 : my_pi (536130) = 44279 := pi_536130
  have hm1_val : my_pi (537166) = 44371 := pi_537166
  rcases le_or_gt m 1035 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 536130 := bound_le_helper m 1035 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1036 ≤ m := hm_gt
    have h1 : 537166 ≤ m*(m+1)/2 := bound_gt_helper m 1036 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_263 (m : ℕ) (hm1 : m ≥ 1) : my_pi (263*264) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 263*264 = 69432 := by decide
  rw [hk_eq]
  have hk : my_pi (69432) = 6892 := pi_69432
  have hm0 : my_pi (535095) = 44203 := pi_535095
  have hm1_val : my_pi (536130) = 44279 := pi_536130
  rcases le_or_gt m 1034 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 535095 := bound_le_helper m 1034 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1035 ≤ m := hm_gt
    have h1 : 536130 ≤ m*(m+1)/2 := bound_gt_helper m 1035 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_264 (m : ℕ) (hm1 : m ≥ 1) : my_pi (264*265) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 264*265 = 69960 := by decide
  rw [hk_eq]
  have hk : my_pi (69960) = 6933 := pi_69960
  have hm0 : my_pi (535095) = 44203 := pi_535095
  have hm1_val : my_pi (536130) = 44279 := pi_536130
  rcases le_or_gt m 1034 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 535095 := bound_le_helper m 1034 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1035 ≤ m := hm_gt
    have h1 : 536130 ≤ m*(m+1)/2 := bound_gt_helper m 1035 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_265 (m : ℕ) (hm1 : m ≥ 1) : my_pi (265*266) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 265*266 = 70490 := by decide
  rw [hk_eq]
  have hk : my_pi (70490) = 6985 := pi_70490
  have hm0 : my_pi (534061) = 44134 := pi_534061
  have hm1_val : my_pi (535095) = 44203 := pi_535095
  rcases le_or_gt m 1033 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 534061 := bound_le_helper m 1033 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1034 ≤ m := hm_gt
    have h1 : 535095 ≤ m*(m+1)/2 := bound_gt_helper m 1034 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_266 (m : ℕ) (hm1 : m ≥ 1) : my_pi (266*267) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 266*267 = 71022 := by decide
  rw [hk_eq]
  have hk : my_pi (71022) = 7034 := pi_71022
  have hm0 : my_pi (533028) = 44055 := pi_533028
  have hm1_val : my_pi (534061) = 44134 := pi_534061
  rcases le_or_gt m 1032 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 533028 := bound_le_helper m 1032 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1033 ≤ m := hm_gt
    have h1 : 534061 ≤ m*(m+1)/2 := bound_gt_helper m 1033 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_267 (m : ℕ) (hm1 : m ≥ 1) : my_pi (267*268) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 267*268 = 71556 := by decide
  rw [hk_eq]
  have hk : my_pi (71556) = 7087 := pi_71556
  have hm0 : my_pi (533028) = 44055 := pi_533028
  have hm1_val : my_pi (534061) = 44134 := pi_534061
  rcases le_or_gt m 1032 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 533028 := bound_le_helper m 1032 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1033 ≤ m := hm_gt
    have h1 : 534061 ≤ m*(m+1)/2 := bound_gt_helper m 1033 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_268 (m : ℕ) (hm1 : m ≥ 1) : my_pi (268*269) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 268*269 = 72092 := by decide
  rw [hk_eq]
  have hk : my_pi (72092) = 7137 := pi_72092
  have hm0 : my_pi (531996) = 43972 := pi_531996
  have hm1_val : my_pi (533028) = 44055 := pi_533028
  rcases le_or_gt m 1031 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 531996 := bound_le_helper m 1031 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1032 ≤ m := hm_gt
    have h1 : 533028 ≤ m*(m+1)/2 := bound_gt_helper m 1032 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_269 (m : ℕ) (hm1 : m ≥ 1) : my_pi (269*270) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 269*270 = 72630 := by decide
  rw [hk_eq]
  have hk : my_pi (72630) = 7181 := pi_72630
  have hm0 : my_pi (531996) = 43972 := pi_531996
  have hm1_val : my_pi (533028) = 44055 := pi_533028
  rcases le_or_gt m 1031 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 531996 := bound_le_helper m 1031 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1032 ≤ m := hm_gt
    have h1 : 533028 ≤ m*(m+1)/2 := bound_gt_helper m 1032 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_270 (m : ℕ) (hm1 : m ≥ 1) : my_pi (270*271) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 270*271 = 73170 := by decide
  rw [hk_eq]
  have hk : my_pi (73170) = 7232 := pi_73170
  have hm0 : my_pi (530965) = 43901 := pi_530965
  have hm1_val : my_pi (531996) = 43972 := pi_531996
  rcases le_or_gt m 1030 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 530965 := bound_le_helper m 1030 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1031 ≤ m := hm_gt
    have h1 : 531996 ≤ m*(m+1)/2 := bound_gt_helper m 1031 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_271 (m : ℕ) (hm1 : m ≥ 1) : my_pi (271*272) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 271*272 = 73712 := by decide
  rw [hk_eq]
  have hk : my_pi (73712) = 7279 := pi_73712
  have hm0 : my_pi (529935) = 43817 := pi_529935
  have hm1_val : my_pi (530965) = 43901 := pi_530965
  rcases le_or_gt m 1029 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 529935 := bound_le_helper m 1029 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1030 ≤ m := hm_gt
    have h1 : 530965 ≤ m*(m+1)/2 := bound_gt_helper m 1030 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_272 (m : ℕ) (hm1 : m ≥ 1) : my_pi (272*273) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 272*273 = 74256 := by decide
  rw [hk_eq]
  have hk : my_pi (74256) = 7325 := pi_74256
  have hm0 : my_pi (529935) = 43817 := pi_529935
  have hm1_val : my_pi (530965) = 43901 := pi_530965
  rcases le_or_gt m 1029 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 529935 := bound_le_helper m 1029 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1030 ≤ m := hm_gt
    have h1 : 530965 ≤ m*(m+1)/2 := bound_gt_helper m 1030 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_273 (m : ℕ) (hm1 : m ≥ 1) : my_pi (273*274) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 273*274 = 74802 := by decide
  rw [hk_eq]
  have hk : my_pi (74802) = 7376 := pi_74802
  have hm0 : my_pi (528906) = 43740 := pi_528906
  have hm1_val : my_pi (529935) = 43817 := pi_529935
  rcases le_or_gt m 1028 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 528906 := bound_le_helper m 1028 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1029 ≤ m := hm_gt
    have h1 : 529935 ≤ m*(m+1)/2 := bound_gt_helper m 1029 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_274 (m : ℕ) (hm1 : m ≥ 1) : my_pi (274*275) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 274*275 = 75350 := by decide
  rw [hk_eq]
  have hk : my_pi (75350) = 7424 := pi_75350
  have hm0 : my_pi (527878) = 43667 := pi_527878
  have hm1_val : my_pi (528906) = 43740 := pi_528906
  rcases le_or_gt m 1027 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 527878 := bound_le_helper m 1027 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1028 ≤ m := hm_gt
    have h1 : 528906 ≤ m*(m+1)/2 := bound_gt_helper m 1028 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_275 (m : ℕ) (hm1 : m ≥ 1) : my_pi (275*276) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 275*276 = 75900 := by decide
  rw [hk_eq]
  have hk : my_pi (75900) = 7474 := pi_75900
  have hm0 : my_pi (527878) = 43667 := pi_527878
  have hm1_val : my_pi (528906) = 43740 := pi_528906
  rcases le_or_gt m 1027 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 527878 := bound_le_helper m 1027 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1028 ≤ m := hm_gt
    have h1 : 528906 ≤ m*(m+1)/2 := bound_gt_helper m 1028 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_276 (m : ℕ) (hm1 : m ≥ 1) : my_pi (276*277) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 276*277 = 76452 := by decide
  rw [hk_eq]
  have hk : my_pi (76452) = 7520 := pi_76452
  have hm0 : my_pi (526851) = 43592 := pi_526851
  have hm1_val : my_pi (527878) = 43667 := pi_527878
  rcases le_or_gt m 1026 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 526851 := bound_le_helper m 1026 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1027 ≤ m := hm_gt
    have h1 : 527878 ≤ m*(m+1)/2 := bound_gt_helper m 1027 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_277 (m : ℕ) (hm1 : m ≥ 1) : my_pi (277*278) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 277*278 = 77006 := by decide
  rw [hk_eq]
  have hk : my_pi (77006) = 7568 := pi_77006
  have hm0 : my_pi (525825) = 43507 := pi_525825
  have hm1_val : my_pi (526851) = 43592 := pi_526851
  rcases le_or_gt m 1025 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 525825 := bound_le_helper m 1025 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1026 ≤ m := hm_gt
    have h1 : 526851 ≤ m*(m+1)/2 := bound_gt_helper m 1026 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_278 (m : ℕ) (hm1 : m ≥ 1) : my_pi (278*279) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 278*279 = 77562 := by decide
  rw [hk_eq]
  have hk : my_pi (77562) = 7621 := pi_77562
  have hm0 : my_pi (525825) = 43507 := pi_525825
  have hm1_val : my_pi (526851) = 43592 := pi_526851
  rcases le_or_gt m 1025 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 525825 := bound_le_helper m 1025 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1026 ≤ m := hm_gt
    have h1 : 526851 ≤ m*(m+1)/2 := bound_gt_helper m 1026 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_279 (m : ℕ) (hm1 : m ≥ 1) : my_pi (279*280) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 279*280 = 78120 := by decide
  rw [hk_eq]
  have hk : my_pi (78120) = 7670 := pi_78120
  have hm0 : my_pi (524800) = 43419 := pi_524800
  have hm1_val : my_pi (525825) = 43507 := pi_525825
  rcases le_or_gt m 1024 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 524800 := bound_le_helper m 1024 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1025 ≤ m := hm_gt
    have h1 : 525825 ≤ m*(m+1)/2 := bound_gt_helper m 1025 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_280 (m : ℕ) (hm1 : m ≥ 1) : my_pi (280*281) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 280*281 = 78680 := by decide
  rw [hk_eq]
  have hk : my_pi (78680) = 7718 := pi_78680
  have hm0 : my_pi (524800) = 43419 := pi_524800
  have hm1_val : my_pi (525825) = 43507 := pi_525825
  rcases le_or_gt m 1024 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 524800 := bound_le_helper m 1024 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1025 ≤ m := hm_gt
    have h1 : 525825 ≤ m*(m+1)/2 := bound_gt_helper m 1025 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_281 (m : ℕ) (hm1 : m ≥ 1) : my_pi (281*282) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 281*282 = 79242 := by decide
  rw [hk_eq]
  have hk : my_pi (79242) = 7766 := pi_79242
  have hm0 : my_pi (523776) = 43350 := pi_523776
  have hm1_val : my_pi (524800) = 43419 := pi_524800
  rcases le_or_gt m 1023 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 523776 := bound_le_helper m 1023 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1024 ≤ m := hm_gt
    have h1 : 524800 ≤ m*(m+1)/2 := bound_gt_helper m 1024 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_282 (m : ℕ) (hm1 : m ≥ 1) : my_pi (282*283) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 282*283 = 79806 := by decide
  rw [hk_eq]
  have hk : my_pi (79806) = 7814 := pi_79806
  have hm0 : my_pi (522753) = 43276 := pi_522753
  have hm1_val : my_pi (523776) = 43350 := pi_523776
  rcases le_or_gt m 1022 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 522753 := bound_le_helper m 1022 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1023 ≤ m := hm_gt
    have h1 : 523776 ≤ m*(m+1)/2 := bound_gt_helper m 1023 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_283 (m : ℕ) (hm1 : m ≥ 1) : my_pi (283*284) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 283*284 = 80372 := by decide
  rw [hk_eq]
  have hk : my_pi (80372) = 7870 := pi_80372
  have hm0 : my_pi (522753) = 43276 := pi_522753
  have hm1_val : my_pi (523776) = 43350 := pi_523776
  rcases le_or_gt m 1022 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 522753 := bound_le_helper m 1022 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1023 ≤ m := hm_gt
    have h1 : 523776 ≤ m*(m+1)/2 := bound_gt_helper m 1023 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_284 (m : ℕ) (hm1 : m ≥ 1) : my_pi (284*285) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 284*285 = 80940 := by decide
  rw [hk_eq]
  have hk : my_pi (80940) = 7922 := pi_80940
  have hm0 : my_pi (521731) = 43194 := pi_521731
  have hm1_val : my_pi (522753) = 43276 := pi_522753
  rcases le_or_gt m 1021 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 521731 := bound_le_helper m 1021 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1022 ≤ m := hm_gt
    have h1 : 522753 ≤ m*(m+1)/2 := bound_gt_helper m 1022 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_285 (m : ℕ) (hm1 : m ≥ 1) : my_pi (285*286) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 285*286 = 81510 := by decide
  rw [hk_eq]
  have hk : my_pi (81510) = 7971 := pi_81510
  have hm0 : my_pi (520710) = 43114 := pi_520710
  have hm1_val : my_pi (521731) = 43194 := pi_521731
  rcases le_or_gt m 1020 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 520710 := bound_le_helper m 1020 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1021 ≤ m := hm_gt
    have h1 : 521731 ≤ m*(m+1)/2 := bound_gt_helper m 1021 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_286 (m : ℕ) (hm1 : m ≥ 1) : my_pi (286*287) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 286*287 = 82082 := by decide
  rw [hk_eq]
  have hk : my_pi (82082) = 8028 := pi_82082
  have hm0 : my_pi (520710) = 43114 := pi_520710
  have hm1_val : my_pi (521731) = 43194 := pi_521731
  rcases le_or_gt m 1020 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 520710 := bound_le_helper m 1020 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1021 ≤ m := hm_gt
    have h1 : 521731 ≤ m*(m+1)/2 := bound_gt_helper m 1021 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_287 (m : ℕ) (hm1 : m ≥ 1) : my_pi (287*288) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 287*288 = 82656 := by decide
  rw [hk_eq]
  have hk : my_pi (82656) = 8080 := pi_82656
  have hm0 : my_pi (519690) = 43037 := pi_519690
  have hm1_val : my_pi (520710) = 43114 := pi_520710
  rcases le_or_gt m 1019 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 519690 := bound_le_helper m 1019 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1020 ≤ m := hm_gt
    have h1 : 520710 ≤ m*(m+1)/2 := bound_gt_helper m 1020 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_288 (m : ℕ) (hm1 : m ≥ 1) : my_pi (288*289) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 288*289 = 83232 := by decide
  rw [hk_eq]
  have hk : my_pi (83232) = 8126 := pi_83232
  have hm0 : my_pi (518671) = 42956 := pi_518671
  have hm1_val : my_pi (519690) = 43037 := pi_519690
  rcases le_or_gt m 1018 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 518671 := bound_le_helper m 1018 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1019 ≤ m := hm_gt
    have h1 : 519690 ≤ m*(m+1)/2 := bound_gt_helper m 1019 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_289 (m : ℕ) (hm1 : m ≥ 1) : my_pi (289*290) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 289*290 = 83810 := by decide
  rw [hk_eq]
  have hk : my_pi (83810) = 8175 := pi_83810
  have hm0 : my_pi (518671) = 42956 := pi_518671
  have hm1_val : my_pi (519690) = 43037 := pi_519690
  rcases le_or_gt m 1018 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 518671 := bound_le_helper m 1018 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1019 ≤ m := hm_gt
    have h1 : 519690 ≤ m*(m+1)/2 := bound_gt_helper m 1019 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_290 (m : ℕ) (hm1 : m ≥ 1) : my_pi (290*291) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 290*291 = 84390 := by decide
  rw [hk_eq]
  have hk : my_pi (84390) = 8224 := pi_84390
  have hm0 : my_pi (517653) = 42885 := pi_517653
  have hm1_val : my_pi (518671) = 42956 := pi_518671
  rcases le_or_gt m 1017 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 517653 := bound_le_helper m 1017 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1018 ≤ m := hm_gt
    have h1 : 518671 ≤ m*(m+1)/2 := bound_gt_helper m 1018 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_291 (m : ℕ) (hm1 : m ≥ 1) : my_pi (291*292) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 291*292 = 84972 := by decide
  rw [hk_eq]
  have hk : my_pi (84972) = 8274 := pi_84972
  have hm0 : my_pi (516636) = 42794 := pi_516636
  have hm1_val : my_pi (517653) = 42885 := pi_517653
  rcases le_or_gt m 1016 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 516636 := bound_le_helper m 1016 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1017 ≤ m := hm_gt
    have h1 : 517653 ≤ m*(m+1)/2 := bound_gt_helper m 1017 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_292 (m : ℕ) (hm1 : m ≥ 1) : my_pi (292*293) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 292*293 = 85556 := by decide
  rw [hk_eq]
  have hk : my_pi (85556) = 8326 := pi_85556
  have hm0 : my_pi (516636) = 42794 := pi_516636
  have hm1_val : my_pi (517653) = 42885 := pi_517653
  rcases le_or_gt m 1016 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 516636 := bound_le_helper m 1016 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1017 ≤ m := hm_gt
    have h1 : 517653 ≤ m*(m+1)/2 := bound_gt_helper m 1017 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_293 (m : ℕ) (hm1 : m ≥ 1) : my_pi (293*294) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 293*294 = 86142 := by decide
  rw [hk_eq]
  have hk : my_pi (86142) = 8374 := pi_86142
  have hm0 : my_pi (515620) = 42707 := pi_515620
  have hm1_val : my_pi (516636) = 42794 := pi_516636
  rcases le_or_gt m 1015 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 515620 := bound_le_helper m 1015 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1016 ≤ m := hm_gt
    have h1 : 516636 ≤ m*(m+1)/2 := bound_gt_helper m 1016 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_294 (m : ℕ) (hm1 : m ≥ 1) : my_pi (294*295) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 294*295 = 86730 := by decide
  rw [hk_eq]
  have hk : my_pi (86730) = 8429 := pi_86730
  have hm0 : my_pi (515620) = 42707 := pi_515620
  have hm1_val : my_pi (516636) = 42794 := pi_516636
  rcases le_or_gt m 1015 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 515620 := bound_le_helper m 1015 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1016 ≤ m := hm_gt
    have h1 : 516636 ≤ m*(m+1)/2 := bound_gt_helper m 1016 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_295 (m : ℕ) (hm1 : m ≥ 1) : my_pi (295*296) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 295*296 = 87320 := by decide
  rw [hk_eq]
  have hk : my_pi (87320) = 8479 := pi_87320
  have hm0 : my_pi (514605) = 42640 := pi_514605
  have hm1_val : my_pi (515620) = 42707 := pi_515620
  rcases le_or_gt m 1014 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 514605 := bound_le_helper m 1014 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1015 ≤ m := hm_gt
    have h1 : 515620 ≤ m*(m+1)/2 := bound_gt_helper m 1015 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_296 (m : ℕ) (hm1 : m ≥ 1) : my_pi (296*297) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 296*297 = 87912 := by decide
  rw [hk_eq]
  have hk : my_pi (87912) = 8535 := pi_87912
  have hm0 : my_pi (513591) = 42562 := pi_513591
  have hm1_val : my_pi (514605) = 42640 := pi_514605
  rcases le_or_gt m 1013 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 513591 := bound_le_helper m 1013 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1014 ≤ m := hm_gt
    have h1 : 514605 ≤ m*(m+1)/2 := bound_gt_helper m 1014 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_297 (m : ℕ) (hm1 : m ≥ 1) : my_pi (297*298) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 297*298 = 88506 := by decide
  rw [hk_eq]
  have hk : my_pi (88506) = 8577 := pi_88506
  have hm0 : my_pi (513591) = 42562 := pi_513591
  have hm1_val : my_pi (514605) = 42640 := pi_514605
  rcases le_or_gt m 1013 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 513591 := bound_le_helper m 1013 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1014 ≤ m := hm_gt
    have h1 : 514605 ≤ m*(m+1)/2 := bound_gt_helper m 1014 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_298 (m : ℕ) (hm1 : m ≥ 1) : my_pi (298*299) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 298*299 = 89102 := by decide
  rw [hk_eq]
  have hk : my_pi (89102) = 8631 := pi_89102
  have hm0 : my_pi (512578) = 42478 := pi_512578
  have hm1_val : my_pi (513591) = 42562 := pi_513591
  rcases le_or_gt m 1012 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 512578 := bound_le_helper m 1012 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1013 ≤ m := hm_gt
    have h1 : 513591 ≤ m*(m+1)/2 := bound_gt_helper m 1013 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_299 (m : ℕ) (hm1 : m ≥ 1) : my_pi (299*300) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 299*300 = 89700 := by decide
  rw [hk_eq]
  have hk : my_pi (89700) = 8688 := pi_89700
  have hm0 : my_pi (511566) = 42413 := pi_511566
  have hm1_val : my_pi (512578) = 42478 := pi_512578
  rcases le_or_gt m 1011 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 511566 := bound_le_helper m 1011 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1012 ≤ m := hm_gt
    have h1 : 512578 ≤ m*(m+1)/2 := bound_gt_helper m 1012 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_300 (m : ℕ) (hm1 : m ≥ 1) : my_pi (300*301) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 300*301 = 90300 := by decide
  rw [hk_eq]
  have hk : my_pi (90300) = 8745 := pi_90300
  have hm0 : my_pi (510555) = 42334 := pi_510555
  have hm1_val : my_pi (511566) = 42413 := pi_511566
  rcases le_or_gt m 1010 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 510555 := bound_le_helper m 1010 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1011 ≤ m := hm_gt
    have h1 : 511566 ≤ m*(m+1)/2 := bound_gt_helper m 1011 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_301 (m : ℕ) (hm1 : m ≥ 1) : my_pi (301*302) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 301*302 = 90902 := by decide
  rw [hk_eq]
  have hk : my_pi (90902) = 8793 := pi_90902
  have hm0 : my_pi (510555) = 42334 := pi_510555
  have hm1_val : my_pi (511566) = 42413 := pi_511566
  rcases le_or_gt m 1010 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 510555 := bound_le_helper m 1010 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1011 ≤ m := hm_gt
    have h1 : 511566 ≤ m*(m+1)/2 := bound_gt_helper m 1011 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_302 (m : ℕ) (hm1 : m ≥ 1) : my_pi (302*303) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 302*303 = 91506 := by decide
  rw [hk_eq]
  have hk : my_pi (91506) = 8848 := pi_91506
  have hm0 : my_pi (509545) = 42251 := pi_509545
  have hm1_val : my_pi (510555) = 42334 := pi_510555
  rcases le_or_gt m 1009 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 509545 := bound_le_helper m 1009 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1010 ≤ m := hm_gt
    have h1 : 510555 ≤ m*(m+1)/2 := bound_gt_helper m 1010 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_303 (m : ℕ) (hm1 : m ≥ 1) : my_pi (303*304) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 303*304 = 92112 := by decide
  rw [hk_eq]
  have hk : my_pi (92112) = 8896 := pi_92112
  have hm0 : my_pi (509545) = 42251 := pi_509545
  have hm1_val : my_pi (510555) = 42334 := pi_510555
  rcases le_or_gt m 1009 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 509545 := bound_le_helper m 1009 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1010 ≤ m := hm_gt
    have h1 : 510555 ≤ m*(m+1)/2 := bound_gt_helper m 1010 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_304 (m : ℕ) (hm1 : m ≥ 1) : my_pi (304*305) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 304*305 = 92720 := by decide
  rw [hk_eq]
  have hk : my_pi (92720) = 8957 := pi_92720
  have hm0 : my_pi (508536) = 42181 := pi_508536
  have hm1_val : my_pi (509545) = 42251 := pi_509545
  rcases le_or_gt m 1008 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 508536 := bound_le_helper m 1008 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1009 ≤ m := hm_gt
    have h1 : 509545 ≤ m*(m+1)/2 := bound_gt_helper m 1009 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_305 (m : ℕ) (hm1 : m ≥ 1) : my_pi (305*306) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 305*306 = 93330 := by decide
  rw [hk_eq]
  have hk : my_pi (93330) = 9016 := pi_93330
  have hm0 : my_pi (507528) = 42106 := pi_507528
  have hm1_val : my_pi (508536) = 42181 := pi_508536
  rcases le_or_gt m 1007 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 507528 := bound_le_helper m 1007 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1008 ≤ m := hm_gt
    have h1 : 508536 ≤ m*(m+1)/2 := bound_gt_helper m 1008 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_306 (m : ℕ) (hm1 : m ≥ 1) : my_pi (306*307) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 306*307 = 93942 := by decide
  rw [hk_eq]
  have hk : my_pi (93942) = 9064 := pi_93942
  have hm0 : my_pi (506521) = 42029 := pi_506521
  have hm1_val : my_pi (507528) = 42106 := pi_507528
  rcases le_or_gt m 1006 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 506521 := bound_le_helper m 1006 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1007 ≤ m := hm_gt
    have h1 : 507528 ≤ m*(m+1)/2 := bound_gt_helper m 1007 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_307 (m : ℕ) (hm1 : m ≥ 1) : my_pi (307*308) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 307*308 = 94556 := by decide
  rw [hk_eq]
  have hk : my_pi (94556) = 9119 := pi_94556
  have hm0 : my_pi (506521) = 42029 := pi_506521
  have hm1_val : my_pi (507528) = 42106 := pi_507528
  rcases le_or_gt m 1006 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 506521 := bound_le_helper m 1006 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1007 ≤ m := hm_gt
    have h1 : 507528 ≤ m*(m+1)/2 := bound_gt_helper m 1007 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_308 (m : ℕ) (hm1 : m ≥ 1) : my_pi (308*309) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 308*309 = 95172 := by decide
  rw [hk_eq]
  have hk : my_pi (95172) = 9173 := pi_95172
  have hm0 : my_pi (505515) = 41957 := pi_505515
  have hm1_val : my_pi (506521) = 42029 := pi_506521
  rcases le_or_gt m 1005 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 505515 := bound_le_helper m 1005 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1006 ≤ m := hm_gt
    have h1 : 506521 ≤ m*(m+1)/2 := bound_gt_helper m 1006 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_309 (m : ℕ) (hm1 : m ≥ 1) : my_pi (309*310) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 309*310 = 95790 := by decide
  rw [hk_eq]
  have hk : my_pi (95790) = 9232 := pi_95790
  have hm0 : my_pi (504510) = 41871 := pi_504510
  have hm1_val : my_pi (505515) = 41957 := pi_505515
  rcases le_or_gt m 1004 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 504510 := bound_le_helper m 1004 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1005 ≤ m := hm_gt
    have h1 : 505515 ≤ m*(m+1)/2 := bound_gt_helper m 1005 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_310 (m : ℕ) (hm1 : m ≥ 1) : my_pi (310*311) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 310*311 = 96410 := by decide
  rw [hk_eq]
  have hk : my_pi (96410) = 9284 := pi_96410
  have hm0 : my_pi (504510) = 41871 := pi_504510
  have hm1_val : my_pi (505515) = 41957 := pi_505515
  rcases le_or_gt m 1004 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 504510 := bound_le_helper m 1004 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1005 ≤ m := hm_gt
    have h1 : 505515 ≤ m*(m+1)/2 := bound_gt_helper m 1005 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_311 (m : ℕ) (hm1 : m ≥ 1) : my_pi (311*312) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 311*312 = 97032 := by decide
  rw [hk_eq]
  have hk : my_pi (97032) = 9340 := pi_97032
  have hm0 : my_pi (503506) = 41795 := pi_503506
  have hm1_val : my_pi (504510) = 41871 := pi_504510
  rcases le_or_gt m 1003 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 503506 := bound_le_helper m 1003 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1004 ≤ m := hm_gt
    have h1 : 504510 ≤ m*(m+1)/2 := bound_gt_helper m 1004 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_312 (m : ℕ) (hm1 : m ≥ 1) : my_pi (312*313) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 312*313 = 97656 := by decide
  rw [hk_eq]
  have hk : my_pi (97656) = 9391 := pi_97656
  have hm0 : my_pi (502503) = 41724 := pi_502503
  have hm1_val : my_pi (503506) = 41795 := pi_503506
  rcases le_or_gt m 1002 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 502503 := bound_le_helper m 1002 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1003 ≤ m := hm_gt
    have h1 : 503506 ≤ m*(m+1)/2 := bound_gt_helper m 1003 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_313 (m : ℕ) (hm1 : m ≥ 1) : my_pi (313*314) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 313*314 = 98282 := by decide
  rw [hk_eq]
  have hk : my_pi (98282) = 9437 := pi_98282
  have hm0 : my_pi (501501) = 41658 := pi_501501
  have hm1_val : my_pi (502503) = 41724 := pi_502503
  rcases le_or_gt m 1001 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 501501 := bound_le_helper m 1001 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1002 ≤ m := hm_gt
    have h1 : 502503 ≤ m*(m+1)/2 := bound_gt_helper m 1002 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_314 (m : ℕ) (hm1 : m ≥ 1) : my_pi (314*315) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 314*315 = 98910 := by decide
  rw [hk_eq]
  have hk : my_pi (98910) = 9495 := pi_98910
  have hm0 : my_pi (501501) = 41658 := pi_501501
  have hm1_val : my_pi (502503) = 41724 := pi_502503
  rcases le_or_gt m 1001 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 501501 := bound_le_helper m 1001 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1002 ≤ m := hm_gt
    have h1 : 502503 ≤ m*(m+1)/2 := bound_gt_helper m 1002 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_315 (m : ℕ) (hm1 : m ≥ 1) : my_pi (315*316) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 315*316 = 99540 := by decide
  rw [hk_eq]
  have hk : my_pi (99540) = 9550 := pi_99540
  have hm0 : my_pi (500500) = 41579 := pi_500500
  have hm1_val : my_pi (501501) = 41658 := pi_501501
  rcases le_or_gt m 1000 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 500500 := bound_le_helper m 1000 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1001 ≤ m := hm_gt
    have h1 : 501501 ≤ m*(m+1)/2 := bound_gt_helper m 1001 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_316 (m : ℕ) (hm1 : m ≥ 1) : my_pi (316*317) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 316*317 = 100172 := by decide
  rw [hk_eq]
  have hk : my_pi (100172) = 9604 := pi_100172
  have hm0 : my_pi (499500) = 41497 := pi_499500
  have hm1_val : my_pi (500500) = 41579 := pi_500500
  rcases le_or_gt m 999 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 499500 := bound_le_helper m 999 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1000 ≤ m := hm_gt
    have h1 : 500500 ≤ m*(m+1)/2 := bound_gt_helper m 1000 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_317 (m : ℕ) (hm1 : m ≥ 1) : my_pi (317*318) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 317*318 = 100806 := by decide
  rw [hk_eq]
  have hk : my_pi (100806) = 9658 := pi_100806
  have hm0 : my_pi (499500) = 41497 := pi_499500
  have hm1_val : my_pi (500500) = 41579 := pi_500500
  rcases le_or_gt m 999 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 499500 := bound_le_helper m 999 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 1000 ≤ m := hm_gt
    have h1 : 500500 ≤ m*(m+1)/2 := bound_gt_helper m 1000 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_318 (m : ℕ) (hm1 : m ≥ 1) : my_pi (318*319) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 318*319 = 101442 := by decide
  rw [hk_eq]
  have hk : my_pi (101442) = 9714 := pi_101442
  have hm0 : my_pi (498501) = 41418 := pi_498501
  have hm1_val : my_pi (499500) = 41497 := pi_499500
  rcases le_or_gt m 998 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 498501 := bound_le_helper m 998 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 999 ≤ m := hm_gt
    have h1 : 499500 ≤ m*(m+1)/2 := bound_gt_helper m 999 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_319 (m : ℕ) (hm1 : m ≥ 1) : my_pi (319*320) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 319*320 = 102080 := by decide
  rw [hk_eq]
  have hk : my_pi (102080) = 9777 := pi_102080
  have hm0 : my_pi (497503) = 41343 := pi_497503
  have hm1_val : my_pi (498501) = 41418 := pi_498501
  rcases le_or_gt m 997 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 497503 := bound_le_helper m 997 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 998 ≤ m := hm_gt
    have h1 : 498501 ≤ m*(m+1)/2 := bound_gt_helper m 998 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_320 (m : ℕ) (hm1 : m ≥ 1) : my_pi (320*321) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 320*321 = 102720 := by decide
  rw [hk_eq]
  have hk : my_pi (102720) = 9834 := pi_102720
  have hm0 : my_pi (496506) = 41273 := pi_496506
  have hm1_val : my_pi (497503) = 41343 := pi_497503
  rcases le_or_gt m 996 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 496506 := bound_le_helper m 996 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 997 ≤ m := hm_gt
    have h1 : 497503 ≤ m*(m+1)/2 := bound_gt_helper m 997 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_321 (m : ℕ) (hm1 : m ≥ 1) : my_pi (321*322) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 321*322 = 103362 := by decide
  rw [hk_eq]
  have hk : my_pi (103362) = 9879 := pi_103362
  have hm0 : my_pi (496506) = 41273 := pi_496506
  have hm1_val : my_pi (497503) = 41343 := pi_497503
  rcases le_or_gt m 996 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 496506 := bound_le_helper m 996 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 997 ≤ m := hm_gt
    have h1 : 497503 ≤ m*(m+1)/2 := bound_gt_helper m 997 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_322 (m : ℕ) (hm1 : m ≥ 1) : my_pi (322*323) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 322*323 = 104006 := by decide
  rw [hk_eq]
  have hk : my_pi (104006) = 9934 := pi_104006
  have hm0 : my_pi (495510) = 41191 := pi_495510
  have hm1_val : my_pi (496506) = 41273 := pi_496506
  rcases le_or_gt m 995 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 495510 := bound_le_helper m 995 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 996 ≤ m := hm_gt
    have h1 : 496506 ≤ m*(m+1)/2 := bound_gt_helper m 996 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_323 (m : ℕ) (hm1 : m ≥ 1) : my_pi (323*324) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 323*324 = 104652 := by decide
  rw [hk_eq]
  have hk : my_pi (104652) = 9989 := pi_104652
  have hm0 : my_pi (494515) = 41107 := pi_494515
  have hm1_val : my_pi (495510) = 41191 := pi_495510
  rcases le_or_gt m 994 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 494515 := bound_le_helper m 994 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 995 ≤ m := hm_gt
    have h1 : 495510 ≤ m*(m+1)/2 := bound_gt_helper m 995 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_324 (m : ℕ) (hm1 : m ≥ 1) : my_pi (324*325) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 324*325 = 105300 := by decide
  rw [hk_eq]
  have hk : my_pi (105300) = 10045 := pi_105300
  have hm0 : my_pi (494515) = 41107 := pi_494515
  have hm1_val : my_pi (495510) = 41191 := pi_495510
  rcases le_or_gt m 994 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 494515 := bound_le_helper m 994 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 995 ≤ m := hm_gt
    have h1 : 495510 ≤ m*(m+1)/2 := bound_gt_helper m 995 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_325 (m : ℕ) (hm1 : m ≥ 1) : my_pi (325*326) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 325*326 = 105950 := by decide
  rw [hk_eq]
  have hk : my_pi (105950) = 10100 := pi_105950
  have hm0 : my_pi (493521) = 41031 := pi_493521
  have hm1_val : my_pi (494515) = 41107 := pi_494515
  rcases le_or_gt m 993 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 493521 := bound_le_helper m 993 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 994 ≤ m := hm_gt
    have h1 : 494515 ≤ m*(m+1)/2 := bound_gt_helper m 994 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_326 (m : ℕ) (hm1 : m ≥ 1) : my_pi (326*327) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 326*327 = 106602 := by decide
  rw [hk_eq]
  have hk : my_pi (106602) = 10157 := pi_106602
  have hm0 : my_pi (492528) = 40955 := pi_492528
  have hm1_val : my_pi (493521) = 41031 := pi_493521
  rcases le_or_gt m 992 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 492528 := bound_le_helper m 992 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 993 ≤ m := hm_gt
    have h1 : 493521 ≤ m*(m+1)/2 := bound_gt_helper m 993 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_327 (m : ℕ) (hm1 : m ≥ 1) : my_pi (327*328) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 327*328 = 107256 := by decide
  rw [hk_eq]
  have hk : my_pi (107256) = 10219 := pi_107256
  have hm0 : my_pi (491536) = 40885 := pi_491536
  have hm1_val : my_pi (492528) = 40955 := pi_492528
  rcases le_or_gt m 991 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 491536 := bound_le_helper m 991 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 992 ≤ m := hm_gt
    have h1 : 492528 ≤ m*(m+1)/2 := bound_gt_helper m 992 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_328 (m : ℕ) (hm1 : m ≥ 1) : my_pi (328*329) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 328*329 = 107912 := by decide
  rw [hk_eq]
  have hk : my_pi (107912) = 10267 := pi_107912
  have hm0 : my_pi (491536) = 40885 := pi_491536
  have hm1_val : my_pi (492528) = 40955 := pi_492528
  rcases le_or_gt m 991 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 491536 := bound_le_helper m 991 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 992 ≤ m := hm_gt
    have h1 : 492528 ≤ m*(m+1)/2 := bound_gt_helper m 992 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_329 (m : ℕ) (hm1 : m ≥ 1) : my_pi (329*330) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 329*330 = 108570 := by decide
  rw [hk_eq]
  have hk : my_pi (108570) = 10326 := pi_108570
  have hm0 : my_pi (490545) = 40808 := pi_490545
  have hm1_val : my_pi (491536) = 40885 := pi_491536
  rcases le_or_gt m 990 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 490545 := bound_le_helper m 990 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 991 ≤ m := hm_gt
    have h1 : 491536 ≤ m*(m+1)/2 := bound_gt_helper m 991 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_330 (m : ℕ) (hm1 : m ≥ 1) : my_pi (330*331) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 330*331 = 109230 := by decide
  rw [hk_eq]
  have hk : my_pi (109230) = 10386 := pi_109230
  have hm0 : my_pi (489555) = 40731 := pi_489555
  have hm1_val : my_pi (490545) = 40808 := pi_490545
  rcases le_or_gt m 989 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 489555 := bound_le_helper m 989 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 990 ≤ m := hm_gt
    have h1 : 490545 ≤ m*(m+1)/2 := bound_gt_helper m 990 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_331 (m : ℕ) (hm1 : m ≥ 1) : my_pi (331*332) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 331*332 = 109892 := by decide
  rw [hk_eq]
  have hk : my_pi (109892) = 10445 := pi_109892
  have hm0 : my_pi (488566) = 40652 := pi_488566
  have hm1_val : my_pi (489555) = 40731 := pi_489555
  rcases le_or_gt m 988 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 488566 := bound_le_helper m 988 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 989 ≤ m := hm_gt
    have h1 : 489555 ≤ m*(m+1)/2 := bound_gt_helper m 989 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_332 (m : ℕ) (hm1 : m ≥ 1) : my_pi (332*333) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 332*333 = 110556 := by decide
  rw [hk_eq]
  have hk : my_pi (110556) = 10492 := pi_110556
  have hm0 : my_pi (488566) = 40652 := pi_488566
  have hm1_val : my_pi (489555) = 40731 := pi_489555
  rcases le_or_gt m 988 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 488566 := bound_le_helper m 988 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 989 ≤ m := hm_gt
    have h1 : 489555 ≤ m*(m+1)/2 := bound_gt_helper m 989 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_333 (m : ℕ) (hm1 : m ≥ 1) : my_pi (333*334) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 333*334 = 111222 := by decide
  rw [hk_eq]
  have hk : my_pi (111222) = 10553 := pi_111222
  have hm0 : my_pi (487578) = 40570 := pi_487578
  have hm1_val : my_pi (488566) = 40652 := pi_488566
  rcases le_or_gt m 987 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 487578 := bound_le_helper m 987 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 988 ≤ m := hm_gt
    have h1 : 488566 ≤ m*(m+1)/2 := bound_gt_helper m 988 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_334 (m : ℕ) (hm1 : m ≥ 1) : my_pi (334*335) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 334*335 = 111890 := by decide
  rw [hk_eq]
  have hk : my_pi (111890) = 10611 := pi_111890
  have hm0 : my_pi (486591) = 40494 := pi_486591
  have hm1_val : my_pi (487578) = 40570 := pi_487578
  rcases le_or_gt m 986 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 486591 := bound_le_helper m 986 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 987 ≤ m := hm_gt
    have h1 : 487578 ≤ m*(m+1)/2 := bound_gt_helper m 987 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_335 (m : ℕ) (hm1 : m ≥ 1) : my_pi (335*336) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 335*336 = 112560 := by decide
  rw [hk_eq]
  have hk : my_pi (112560) = 10666 := pi_112560
  have hm0 : my_pi (485605) = 40422 := pi_485605
  have hm1_val : my_pi (486591) = 40494 := pi_486591
  rcases le_or_gt m 985 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 485605 := bound_le_helper m 985 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 986 ≤ m := hm_gt
    have h1 : 486591 ≤ m*(m+1)/2 := bound_gt_helper m 986 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_336 (m : ℕ) (hm1 : m ≥ 1) : my_pi (336*337) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 336*337 = 113232 := by decide
  rw [hk_eq]
  have hk : my_pi (113232) = 10732 := pi_113232
  have hm0 : my_pi (485605) = 40422 := pi_485605
  have hm1_val : my_pi (486591) = 40494 := pi_486591
  rcases le_or_gt m 985 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 485605 := bound_le_helper m 985 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 986 ≤ m := hm_gt
    have h1 : 486591 ≤ m*(m+1)/2 := bound_gt_helper m 986 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_337 (m : ℕ) (hm1 : m ≥ 1) : my_pi (337*338) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 337*338 = 113906 := by decide
  rw [hk_eq]
  have hk : my_pi (113906) = 10780 := pi_113906
  have hm0 : my_pi (484620) = 40363 := pi_484620
  have hm1_val : my_pi (485605) = 40422 := pi_485605
  rcases le_or_gt m 984 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 484620 := bound_le_helper m 984 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 985 ≤ m := hm_gt
    have h1 : 485605 ≤ m*(m+1)/2 := bound_gt_helper m 985 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_338 (m : ℕ) (hm1 : m ≥ 1) : my_pi (338*339) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 338*339 = 114582 := by decide
  rw [hk_eq]
  have hk : my_pi (114582) = 10834 := pi_114582
  have hm0 : my_pi (483636) = 40288 := pi_483636
  have hm1_val : my_pi (484620) = 40363 := pi_484620
  rcases le_or_gt m 983 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 483636 := bound_le_helper m 983 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 984 ≤ m := hm_gt
    have h1 : 484620 ≤ m*(m+1)/2 := bound_gt_helper m 984 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_339 (m : ℕ) (hm1 : m ≥ 1) : my_pi (339*340) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 339*340 = 115260 := by decide
  rw [hk_eq]
  have hk : my_pi (115260) = 10894 := pi_115260
  have hm0 : my_pi (482653) = 40212 := pi_482653
  have hm1_val : my_pi (483636) = 40288 := pi_483636
  rcases le_or_gt m 982 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 482653 := bound_le_helper m 982 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 983 ≤ m := hm_gt
    have h1 : 483636 ≤ m*(m+1)/2 := bound_gt_helper m 983 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_340 (m : ℕ) (hm1 : m ≥ 1) : my_pi (340*341) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 340*341 = 115940 := by decide
  rw [hk_eq]
  have hk : my_pi (115940) = 10960 := pi_115940
  have hm0 : my_pi (481671) = 40135 := pi_481671
  have hm1_val : my_pi (482653) = 40212 := pi_482653
  rcases le_or_gt m 981 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 481671 := bound_le_helper m 981 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 982 ≤ m := hm_gt
    have h1 : 482653 ≤ m*(m+1)/2 := bound_gt_helper m 982 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_341 (m : ℕ) (hm1 : m ≥ 1) : my_pi (341*342) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 341*342 = 116622 := by decide
  rw [hk_eq]
  have hk : my_pi (116622) = 11012 := pi_116622
  have hm0 : my_pi (481671) = 40135 := pi_481671
  have hm1_val : my_pi (482653) = 40212 := pi_482653
  rcases le_or_gt m 981 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 481671 := bound_le_helper m 981 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 982 ≤ m := hm_gt
    have h1 : 482653 ≤ m*(m+1)/2 := bound_gt_helper m 982 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_342 (m : ℕ) (hm1 : m ≥ 1) : my_pi (342*343) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 342*343 = 117306 := by decide
  rw [hk_eq]
  have hk : my_pi (117306) = 11070 := pi_117306
  have hm0 : my_pi (480690) = 40060 := pi_480690
  have hm1_val : my_pi (481671) = 40135 := pi_481671
  rcases le_or_gt m 980 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 480690 := bound_le_helper m 980 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 981 ≤ m := hm_gt
    have h1 : 481671 ≤ m*(m+1)/2 := bound_gt_helper m 981 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_343 (m : ℕ) (hm1 : m ≥ 1) : my_pi (343*344) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 343*344 = 117992 := by decide
  rw [hk_eq]
  have hk : my_pi (117992) = 11135 := pi_117992
  have hm0 : my_pi (479710) = 39983 := pi_479710
  have hm1_val : my_pi (480690) = 40060 := pi_480690
  rcases le_or_gt m 979 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 479710 := bound_le_helper m 979 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 980 ≤ m := hm_gt
    have h1 : 480690 ≤ m*(m+1)/2 := bound_gt_helper m 980 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_344 (m : ℕ) (hm1 : m ≥ 1) : my_pi (344*345) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 344*345 = 118680 := by decide
  rw [hk_eq]
  have hk : my_pi (118680) = 11187 := pi_118680
  have hm0 : my_pi (478731) = 39907 := pi_478731
  have hm1_val : my_pi (479710) = 39983 := pi_479710
  rcases le_or_gt m 978 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 478731 := bound_le_helper m 978 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 979 ≤ m := hm_gt
    have h1 : 479710 ≤ m*(m+1)/2 := bound_gt_helper m 979 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_345 (m : ℕ) (hm1 : m ≥ 1) : my_pi (345*346) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 345*346 = 119370 := by decide
  rw [hk_eq]
  have hk : my_pi (119370) = 11246 := pi_119370
  have hm0 : my_pi (478731) = 39907 := pi_478731
  have hm1_val : my_pi (479710) = 39983 := pi_479710
  rcases le_or_gt m 978 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 478731 := bound_le_helper m 978 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 979 ≤ m := hm_gt
    have h1 : 479710 ≤ m*(m+1)/2 := bound_gt_helper m 979 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_346 (m : ℕ) (hm1 : m ≥ 1) : my_pi (346*347) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 346*347 = 120062 := by decide
  rw [hk_eq]
  have hk : my_pi (120062) = 11306 := pi_120062
  have hm0 : my_pi (477753) = 39829 := pi_477753
  have hm1_val : my_pi (478731) = 39907 := pi_478731
  rcases le_or_gt m 977 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 477753 := bound_le_helper m 977 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 978 ≤ m := hm_gt
    have h1 : 478731 ≤ m*(m+1)/2 := bound_gt_helper m 978 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_347 (m : ℕ) (hm1 : m ≥ 1) : my_pi (347*348) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 347*348 = 120756 := by decide
  rw [hk_eq]
  have hk : my_pi (120756) = 11364 := pi_120756
  have hm0 : my_pi (476776) = 39765 := pi_476776
  have hm1_val : my_pi (477753) = 39829 := pi_477753
  rcases le_or_gt m 976 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 476776 := bound_le_helper m 976 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 977 ≤ m := hm_gt
    have h1 : 477753 ≤ m*(m+1)/2 := bound_gt_helper m 977 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_348 (m : ℕ) (hm1 : m ≥ 1) : my_pi (348*349) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 348*349 = 121452 := by decide
  rw [hk_eq]
  have hk : my_pi (121452) = 11430 := pi_121452
  have hm0 : my_pi (475800) = 39686 := pi_475800
  have hm1_val : my_pi (476776) = 39765 := pi_476776
  rcases le_or_gt m 975 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 475800 := bound_le_helper m 975 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 976 ≤ m := hm_gt
    have h1 : 476776 ≤ m*(m+1)/2 := bound_gt_helper m 976 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_349 (m : ℕ) (hm1 : m ≥ 1) : my_pi (349*350) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 349*350 = 122150 := by decide
  rw [hk_eq]
  have hk : my_pi (122150) = 11491 := pi_122150
  have hm0 : my_pi (474825) = 39604 := pi_474825
  have hm1_val : my_pi (475800) = 39686 := pi_475800
  rcases le_or_gt m 974 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 474825 := bound_le_helper m 974 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 975 ≤ m := hm_gt
    have h1 : 475800 ≤ m*(m+1)/2 := bound_gt_helper m 975 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_350 (m : ℕ) (hm1 : m ≥ 1) : my_pi (350*351) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 350*351 = 122850 := by decide
  rw [hk_eq]
  have hk : my_pi (122850) = 11551 := pi_122850
  have hm0 : my_pi (474825) = 39604 := pi_474825
  have hm1_val : my_pi (475800) = 39686 := pi_475800
  rcases le_or_gt m 974 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 474825 := bound_le_helper m 974 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 975 ≤ m := hm_gt
    have h1 : 475800 ≤ m*(m+1)/2 := bound_gt_helper m 975 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_351 (m : ℕ) (hm1 : m ≥ 1) : my_pi (351*352) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 351*352 = 123552 := by decide
  rw [hk_eq]
  have hk : my_pi (123552) = 11611 := pi_123552
  have hm0 : my_pi (473851) = 39523 := pi_473851
  have hm1_val : my_pi (474825) = 39604 := pi_474825
  rcases le_or_gt m 973 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 473851 := bound_le_helper m 973 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 974 ≤ m := hm_gt
    have h1 : 474825 ≤ m*(m+1)/2 := bound_gt_helper m 974 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_352 (m : ℕ) (hm1 : m ≥ 1) : my_pi (352*353) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 352*353 = 124256 := by decide
  rw [hk_eq]
  have hk : my_pi (124256) = 11671 := pi_124256
  have hm0 : my_pi (472878) = 39453 := pi_472878
  have hm1_val : my_pi (473851) = 39523 := pi_473851
  rcases le_or_gt m 972 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 472878 := bound_le_helper m 972 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 973 ≤ m := hm_gt
    have h1 : 473851 ≤ m*(m+1)/2 := bound_gt_helper m 973 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_353 (m : ℕ) (hm1 : m ≥ 1) : my_pi (353*354) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 353*354 = 124962 := by decide
  rw [hk_eq]
  have hk : my_pi (124962) = 11730 := pi_124962
  have hm0 : my_pi (471906) = 39380 := pi_471906
  have hm1_val : my_pi (472878) = 39453 := pi_472878
  rcases le_or_gt m 971 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 471906 := bound_le_helper m 971 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 972 ≤ m := hm_gt
    have h1 : 472878 ≤ m*(m+1)/2 := bound_gt_helper m 972 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_354 (m : ℕ) (hm1 : m ≥ 1) : my_pi (354*355) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 354*355 = 125670 := by decide
  rw [hk_eq]
  have hk : my_pi (125670) = 11791 := pi_125670
  have hm0 : my_pi (470935) = 39304 := pi_470935
  have hm1_val : my_pi (471906) = 39380 := pi_471906
  rcases le_or_gt m 970 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 470935 := bound_le_helper m 970 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 971 ≤ m := hm_gt
    have h1 : 471906 ≤ m*(m+1)/2 := bound_gt_helper m 971 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_355 (m : ℕ) (hm1 : m ≥ 1) : my_pi (355*356) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 355*356 = 126380 := by decide
  rw [hk_eq]
  have hk : my_pi (126380) = 11853 := pi_126380
  have hm0 : my_pi (469965) = 39220 := pi_469965
  have hm1_val : my_pi (470935) = 39304 := pi_470935
  rcases le_or_gt m 969 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 469965 := bound_le_helper m 969 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 970 ≤ m := hm_gt
    have h1 : 470935 ≤ m*(m+1)/2 := bound_gt_helper m 970 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_356 (m : ℕ) (hm1 : m ≥ 1) : my_pi (356*357) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 356*357 = 127092 := by decide
  rw [hk_eq]
  have hk : my_pi (127092) = 11907 := pi_127092
  have hm0 : my_pi (469965) = 39220 := pi_469965
  have hm1_val : my_pi (470935) = 39304 := pi_470935
  rcases le_or_gt m 969 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 469965 := bound_le_helper m 969 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 970 ≤ m := hm_gt
    have h1 : 470935 ≤ m*(m+1)/2 := bound_gt_helper m 970 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_357 (m : ℕ) (hm1 : m ≥ 1) : my_pi (357*358) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 357*358 = 127806 := by decide
  rw [hk_eq]
  have hk : my_pi (127806) = 11970 := pi_127806
  have hm0 : my_pi (468996) = 39151 := pi_468996
  have hm1_val : my_pi (469965) = 39220 := pi_469965
  rcases le_or_gt m 968 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 468996 := bound_le_helper m 968 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 969 ≤ m := hm_gt
    have h1 : 469965 ≤ m*(m+1)/2 := bound_gt_helper m 969 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_358 (m : ℕ) (hm1 : m ≥ 1) : my_pi (358*359) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 358*359 = 128522 := by decide
  rw [hk_eq]
  have hk : my_pi (128522) = 12035 := pi_128522
  have hm0 : my_pi (468028) = 39069 := pi_468028
  have hm1_val : my_pi (468996) = 39151 := pi_468996
  rcases le_or_gt m 967 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 468028 := bound_le_helper m 967 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 968 ≤ m := hm_gt
    have h1 : 468996 ≤ m*(m+1)/2 := bound_gt_helper m 968 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_359 (m : ℕ) (hm1 : m ≥ 1) : my_pi (359*360) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 359*360 = 129240 := by decide
  rw [hk_eq]
  have hk : my_pi (129240) = 12097 := pi_129240
  have hm0 : my_pi (467061) = 38987 := pi_467061
  have hm1_val : my_pi (468028) = 39069 := pi_468028
  rcases le_or_gt m 966 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 467061 := bound_le_helper m 966 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 967 ≤ m := hm_gt
    have h1 : 468028 ≤ m*(m+1)/2 := bound_gt_helper m 967 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_360 (m : ℕ) (hm1 : m ≥ 1) : my_pi (360*361) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 360*361 = 129960 := by decide
  rw [hk_eq]
  have hk : my_pi (129960) = 12157 := pi_129960
  have hm0 : my_pi (467061) = 38987 := pi_467061
  have hm1_val : my_pi (468028) = 39069 := pi_468028
  rcases le_or_gt m 966 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 467061 := bound_le_helper m 966 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 967 ≤ m := hm_gt
    have h1 : 468028 ≤ m*(m+1)/2 := bound_gt_helper m 967 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_361 (m : ℕ) (hm1 : m ≥ 1) : my_pi (361*362) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 361*362 = 130682 := by decide
  rw [hk_eq]
  have hk : my_pi (130682) = 12223 := pi_130682
  have hm0 : my_pi (466095) = 38925 := pi_466095
  have hm1_val : my_pi (467061) = 38987 := pi_467061
  rcases le_or_gt m 965 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 466095 := bound_le_helper m 965 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 966 ≤ m := hm_gt
    have h1 : 467061 ≤ m*(m+1)/2 := bound_gt_helper m 966 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_362 (m : ℕ) (hm1 : m ≥ 1) : my_pi (362*363) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 362*363 = 131406 := by decide
  rw [hk_eq]
  have hk : my_pi (131406) = 12275 := pi_131406
  have hm0 : my_pi (465130) = 38853 := pi_465130
  have hm1_val : my_pi (466095) = 38925 := pi_466095
  rcases le_or_gt m 964 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 465130 := bound_le_helper m 964 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 965 ≤ m := hm_gt
    have h1 : 466095 ≤ m*(m+1)/2 := bound_gt_helper m 965 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_363 (m : ℕ) (hm1 : m ≥ 1) : my_pi (363*364) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 363*364 = 132132 := by decide
  rw [hk_eq]
  have hk : my_pi (132132) = 12336 := pi_132132
  have hm0 : my_pi (464166) = 38769 := pi_464166
  have hm1_val : my_pi (465130) = 38853 := pi_465130
  rcases le_or_gt m 963 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 464166 := bound_le_helper m 963 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 964 ≤ m := hm_gt
    have h1 : 465130 ≤ m*(m+1)/2 := bound_gt_helper m 964 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_364 (m : ℕ) (hm1 : m ≥ 1) : my_pi (364*365) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 364*365 = 132860 := by decide
  rw [hk_eq]
  have hk : my_pi (132860) = 12402 := pi_132860
  have hm0 : my_pi (463203) = 38686 := pi_463203
  have hm1_val : my_pi (464166) = 38769 := pi_464166
  rcases le_or_gt m 962 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 463203 := bound_le_helper m 962 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 963 ≤ m := hm_gt
    have h1 : 464166 ≤ m*(m+1)/2 := bound_gt_helper m 963 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_365 (m : ℕ) (hm1 : m ≥ 1) : my_pi (365*366) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 365*366 = 133590 := by decide
  rw [hk_eq]
  have hk : my_pi (133590) = 12464 := pi_133590
  have hm0 : my_pi (463203) = 38686 := pi_463203
  have hm1_val : my_pi (464166) = 38769 := pi_464166
  rcases le_or_gt m 962 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 463203 := bound_le_helper m 962 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 963 ≤ m := hm_gt
    have h1 : 464166 ≤ m*(m+1)/2 := bound_gt_helper m 963 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_366 (m : ℕ) (hm1 : m ≥ 1) : my_pi (366*367) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 366*367 = 134322 := by decide
  rw [hk_eq]
  have hk : my_pi (134322) = 12523 := pi_134322
  have hm0 : my_pi (462241) = 38620 := pi_462241
  have hm1_val : my_pi (463203) = 38686 := pi_463203
  rcases le_or_gt m 961 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 462241 := bound_le_helper m 961 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 962 ≤ m := hm_gt
    have h1 : 463203 ≤ m*(m+1)/2 := bound_gt_helper m 962 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_367 (m : ℕ) (hm1 : m ≥ 1) : my_pi (367*368) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 367*368 = 135056 := by decide
  rw [hk_eq]
  have hk : my_pi (135056) = 12582 := pi_135056
  have hm0 : my_pi (461280) = 38555 := pi_461280
  have hm1_val : my_pi (462241) = 38620 := pi_462241
  rcases le_or_gt m 960 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 461280 := bound_le_helper m 960 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 961 ≤ m := hm_gt
    have h1 : 462241 ≤ m*(m+1)/2 := bound_gt_helper m 961 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_368 (m : ℕ) (hm1 : m ≥ 1) : my_pi (368*369) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 368*369 = 135792 := by decide
  rw [hk_eq]
  have hk : my_pi (135792) = 12651 := pi_135792
  have hm0 : my_pi (460320) = 38483 := pi_460320
  have hm1_val : my_pi (461280) = 38555 := pi_461280
  rcases le_or_gt m 959 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 460320 := bound_le_helper m 959 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 960 ≤ m := hm_gt
    have h1 : 461280 ≤ m*(m+1)/2 := bound_gt_helper m 960 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_369 (m : ℕ) (hm1 : m ≥ 1) : my_pi (369*370) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 369*370 = 136530 := by decide
  rw [hk_eq]
  have hk : my_pi (136530) = 12717 := pi_136530
  have hm0 : my_pi (459361) = 38418 := pi_459361
  have hm1_val : my_pi (460320) = 38483 := pi_460320
  rcases le_or_gt m 958 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 459361 := bound_le_helper m 958 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 959 ≤ m := hm_gt
    have h1 : 460320 ≤ m*(m+1)/2 := bound_gt_helper m 959 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_370 (m : ℕ) (hm1 : m ≥ 1) : my_pi (370*371) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 370*371 = 137270 := by decide
  rw [hk_eq]
  have hk : my_pi (137270) = 12780 := pi_137270
  have hm0 : my_pi (458403) = 38343 := pi_458403
  have hm1_val : my_pi (459361) = 38418 := pi_459361
  rcases le_or_gt m 957 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 458403 := bound_le_helper m 957 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 958 ≤ m := hm_gt
    have h1 : 459361 ≤ m*(m+1)/2 := bound_gt_helper m 958 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_371 (m : ℕ) (hm1 : m ≥ 1) : my_pi (371*372) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 371*372 = 138012 := by decide
  rw [hk_eq]
  have hk : my_pi (138012) = 12842 := pi_138012
  have hm0 : my_pi (457446) = 38278 := pi_457446
  have hm1_val : my_pi (458403) = 38343 := pi_458403
  rcases le_or_gt m 956 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 457446 := bound_le_helper m 956 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 957 ≤ m := hm_gt
    have h1 : 458403 ≤ m*(m+1)/2 := bound_gt_helper m 957 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_372 (m : ℕ) (hm1 : m ≥ 1) : my_pi (372*373) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 372*373 = 138756 := by decide
  rw [hk_eq]
  have hk : my_pi (138756) = 12907 := pi_138756
  have hm0 : my_pi (456490) = 38196 := pi_456490
  have hm1_val : my_pi (457446) = 38278 := pi_457446
  rcases le_or_gt m 955 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 456490 := bound_le_helper m 955 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 956 ≤ m := hm_gt
    have h1 : 457446 ≤ m*(m+1)/2 := bound_gt_helper m 956 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_373 (m : ℕ) (hm1 : m ≥ 1) : my_pi (373*374) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 373*374 = 139502 := by decide
  rw [hk_eq]
  have hk : my_pi (139502) = 12968 := pi_139502
  have hm0 : my_pi (455535) = 38129 := pi_455535
  have hm1_val : my_pi (456490) = 38196 := pi_456490
  rcases le_or_gt m 954 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 455535 := bound_le_helper m 954 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 955 ≤ m := hm_gt
    have h1 : 456490 ≤ m*(m+1)/2 := bound_gt_helper m 955 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_374 (m : ℕ) (hm1 : m ≥ 1) : my_pi (374*375) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 374*375 = 140250 := by decide
  rw [hk_eq]
  have hk : my_pi (140250) = 13029 := pi_140250
  have hm0 : my_pi (454581) = 38053 := pi_454581
  have hm1_val : my_pi (455535) = 38129 := pi_455535
  rcases le_or_gt m 953 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 454581 := bound_le_helper m 953 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 954 ≤ m := hm_gt
    have h1 : 455535 ≤ m*(m+1)/2 := bound_gt_helper m 954 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_375 (m : ℕ) (hm1 : m ≥ 1) : my_pi (375*376) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 375*376 = 141000 := by decide
  rw [hk_eq]
  have hk : my_pi (141000) = 13097 := pi_141000
  have hm0 : my_pi (454581) = 38053 := pi_454581
  have hm1_val : my_pi (455535) = 38129 := pi_455535
  rcases le_or_gt m 953 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 454581 := bound_le_helper m 953 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 954 ≤ m := hm_gt
    have h1 : 455535 ≤ m*(m+1)/2 := bound_gt_helper m 954 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_376 (m : ℕ) (hm1 : m ≥ 1) : my_pi (376*377) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 376*377 = 141752 := by decide
  rw [hk_eq]
  have hk : my_pi (141752) = 13162 := pi_141752
  have hm0 : my_pi (453628) = 37979 := pi_453628
  have hm1_val : my_pi (454581) = 38053 := pi_454581
  rcases le_or_gt m 952 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 453628 := bound_le_helper m 952 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 953 ≤ m := hm_gt
    have h1 : 454581 ≤ m*(m+1)/2 := bound_gt_helper m 953 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_377 (m : ℕ) (hm1 : m ≥ 1) : my_pi (377*378) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 377*378 = 142506 := by decide
  rw [hk_eq]
  have hk : my_pi (142506) = 13223 := pi_142506
  have hm0 : my_pi (452676) = 37918 := pi_452676
  have hm1_val : my_pi (453628) = 37979 := pi_453628
  rcases le_or_gt m 951 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 452676 := bound_le_helper m 951 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 952 ≤ m := hm_gt
    have h1 : 453628 ≤ m*(m+1)/2 := bound_gt_helper m 952 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_378 (m : ℕ) (hm1 : m ≥ 1) : my_pi (378*379) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 378*379 = 143262 := by decide
  rw [hk_eq]
  have hk : my_pi (143262) = 13282 := pi_143262
  have hm0 : my_pi (451725) = 37851 := pi_451725
  have hm1_val : my_pi (452676) = 37918 := pi_452676
  rcases le_or_gt m 950 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 451725 := bound_le_helper m 950 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 951 ≤ m := hm_gt
    have h1 : 452676 ≤ m*(m+1)/2 := bound_gt_helper m 951 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_379 (m : ℕ) (hm1 : m ≥ 1) : my_pi (379*380) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 379*380 = 144020 := by decide
  rw [hk_eq]
  have hk : my_pi (144020) = 13344 := pi_144020
  have hm0 : my_pi (450775) = 37773 := pi_450775
  have hm1_val : my_pi (451725) = 37851 := pi_451725
  rcases le_or_gt m 949 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 450775 := bound_le_helper m 949 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 950 ≤ m := hm_gt
    have h1 : 451725 ≤ m*(m+1)/2 := bound_gt_helper m 950 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_380 (m : ℕ) (hm1 : m ≥ 1) : my_pi (380*381) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 380*381 = 144780 := by decide
  rw [hk_eq]
  have hk : my_pi (144780) = 13406 := pi_144780
  have hm0 : my_pi (449826) = 37694 := pi_449826
  have hm1_val : my_pi (450775) = 37773 := pi_450775
  rcases le_or_gt m 948 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 449826 := bound_le_helper m 948 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 949 ≤ m := hm_gt
    have h1 : 450775 ≤ m*(m+1)/2 := bound_gt_helper m 949 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_381 (m : ℕ) (hm1 : m ≥ 1) : my_pi (381*382) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 381*382 = 145542 := by decide
  rw [hk_eq]
  have hk : my_pi (145542) = 13467 := pi_145542
  have hm0 : my_pi (448878) = 37617 := pi_448878
  have hm1_val : my_pi (449826) = 37694 := pi_449826
  rcases le_or_gt m 947 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 448878 := bound_le_helper m 947 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 948 ≤ m := hm_gt
    have h1 : 449826 ≤ m*(m+1)/2 := bound_gt_helper m 948 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_382 (m : ℕ) (hm1 : m ≥ 1) : my_pi (382*383) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 382*383 = 146306 := by decide
  rw [hk_eq]
  have hk : my_pi (146306) = 13534 := pi_146306
  have hm0 : my_pi (448878) = 37617 := pi_448878
  have hm1_val : my_pi (449826) = 37694 := pi_449826
  rcases le_or_gt m 947 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 448878 := bound_le_helper m 947 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 948 ≤ m := hm_gt
    have h1 : 449826 ≤ m*(m+1)/2 := bound_gt_helper m 948 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_383 (m : ℕ) (hm1 : m ≥ 1) : my_pi (383*384) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 383*384 = 147072 := by decide
  rw [hk_eq]
  have hk : my_pi (147072) = 13595 := pi_147072
  have hm0 : my_pi (447931) = 37552 := pi_447931
  have hm1_val : my_pi (448878) = 37617 := pi_448878
  rcases le_or_gt m 946 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 447931 := bound_le_helper m 946 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 947 ≤ m := hm_gt
    have h1 : 448878 ≤ m*(m+1)/2 := bound_gt_helper m 947 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_384 (m : ℕ) (hm1 : m ≥ 1) : my_pi (384*385) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 384*385 = 147840 := by decide
  rw [hk_eq]
  have hk : my_pi (147840) = 13665 := pi_147840
  have hm0 : my_pi (446985) = 37483 := pi_446985
  have hm1_val : my_pi (447931) = 37552 := pi_447931
  rcases le_or_gt m 945 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 446985 := bound_le_helper m 945 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 946 ≤ m := hm_gt
    have h1 : 447931 ≤ m*(m+1)/2 := bound_gt_helper m 946 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_385 (m : ℕ) (hm1 : m ≥ 1) : my_pi (385*386) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 385*386 = 148610 := by decide
  rw [hk_eq]
  have hk : my_pi (148610) = 13722 := pi_148610
  have hm0 : my_pi (446040) = 37417 := pi_446040
  have hm1_val : my_pi (446985) = 37483 := pi_446985
  rcases le_or_gt m 944 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 446040 := bound_le_helper m 944 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 945 ≤ m := hm_gt
    have h1 : 446985 ≤ m*(m+1)/2 := bound_gt_helper m 945 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_386 (m : ℕ) (hm1 : m ≥ 1) : my_pi (386*387) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 386*387 = 149382 := by decide
  rw [hk_eq]
  have hk : my_pi (149382) = 13795 := pi_149382
  have hm0 : my_pi (445096) = 37355 := pi_445096
  have hm1_val : my_pi (446040) = 37417 := pi_446040
  rcases le_or_gt m 943 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 445096 := bound_le_helper m 943 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 944 ≤ m := hm_gt
    have h1 : 446040 ≤ m*(m+1)/2 := bound_gt_helper m 944 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_387 (m : ℕ) (hm1 : m ≥ 1) : my_pi (387*388) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 387*388 = 150156 := by decide
  rw [hk_eq]
  have hk : my_pi (150156) = 13862 := pi_150156
  have hm0 : my_pi (444153) = 37278 := pi_444153
  have hm1_val : my_pi (445096) = 37355 := pi_445096
  rcases le_or_gt m 942 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 444153 := bound_le_helper m 942 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 943 ≤ m := hm_gt
    have h1 : 445096 ≤ m*(m+1)/2 := bound_gt_helper m 943 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_388 (m : ℕ) (hm1 : m ≥ 1) : my_pi (388*389) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 388*389 = 150932 := by decide
  rw [hk_eq]
  have hk : my_pi (150932) = 13927 := pi_150932
  have hm0 : my_pi (443211) = 37197 := pi_443211
  have hm1_val : my_pi (444153) = 37278 := pi_444153
  rcases le_or_gt m 941 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 443211 := bound_le_helper m 941 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 942 ≤ m := hm_gt
    have h1 : 444153 ≤ m*(m+1)/2 := bound_gt_helper m 942 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_389 (m : ℕ) (hm1 : m ≥ 1) : my_pi (389*390) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 389*390 = 151710 := by decide
  rw [hk_eq]
  have hk : my_pi (151710) = 14000 := pi_151710
  have hm0 : my_pi (442270) = 37118 := pi_442270
  have hm1_val : my_pi (443211) = 37197 := pi_443211
  rcases le_or_gt m 940 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 442270 := bound_le_helper m 940 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 941 ≤ m := hm_gt
    have h1 : 443211 ≤ m*(m+1)/2 := bound_gt_helper m 941 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_390 (m : ℕ) (hm1 : m ≥ 1) : my_pi (390*391) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 390*391 = 152490 := by decide
  rw [hk_eq]
  have hk : my_pi (152490) = 14065 := pi_152490
  have hm0 : my_pi (441330) = 37047 := pi_441330
  have hm1_val : my_pi (442270) = 37118 := pi_442270
  rcases le_or_gt m 939 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 441330 := bound_le_helper m 939 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 940 ≤ m := hm_gt
    have h1 : 442270 ≤ m*(m+1)/2 := bound_gt_helper m 940 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_391 (m : ℕ) (hm1 : m ≥ 1) : my_pi (391*392) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 391*392 = 153272 := by decide
  rw [hk_eq]
  have hk : my_pi (153272) = 14128 := pi_153272
  have hm0 : my_pi (440391) = 36971 := pi_440391
  have hm1_val : my_pi (441330) = 37047 := pi_441330
  rcases le_or_gt m 938 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 440391 := bound_le_helper m 938 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 939 ≤ m := hm_gt
    have h1 : 441330 ≤ m*(m+1)/2 := bound_gt_helper m 939 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_392 (m : ℕ) (hm1 : m ≥ 1) : my_pi (392*393) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 392*393 = 154056 := by decide
  rw [hk_eq]
  have hk : my_pi (154056) = 14191 := pi_154056
  have hm0 : my_pi (439453) = 36894 := pi_439453
  have hm1_val : my_pi (440391) = 36971 := pi_440391
  rcases le_or_gt m 937 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 439453 := bound_le_helper m 937 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 938 ≤ m := hm_gt
    have h1 : 440391 ≤ m*(m+1)/2 := bound_gt_helper m 938 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_393 (m : ℕ) (hm1 : m ≥ 1) : my_pi (393*394) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 393*394 = 154842 := by decide
  rw [hk_eq]
  have hk : my_pi (154842) = 14260 := pi_154842
  have hm0 : my_pi (439453) = 36894 := pi_439453
  have hm1_val : my_pi (440391) = 36971 := pi_440391
  rcases le_or_gt m 937 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 439453 := bound_le_helper m 937 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 938 ≤ m := hm_gt
    have h1 : 440391 ≤ m*(m+1)/2 := bound_gt_helper m 938 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_394 (m : ℕ) (hm1 : m ≥ 1) : my_pi (394*395) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 394*395 = 155630 := by decide
  rw [hk_eq]
  have hk : my_pi (155630) = 14327 := pi_155630
  have hm0 : my_pi (438516) = 36825 := pi_438516
  have hm1_val : my_pi (439453) = 36894 := pi_439453
  rcases le_or_gt m 936 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 438516 := bound_le_helper m 936 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 937 ≤ m := hm_gt
    have h1 : 439453 ≤ m*(m+1)/2 := bound_gt_helper m 937 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_395 (m : ℕ) (hm1 : m ≥ 1) : my_pi (395*396) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 395*396 = 156420 := by decide
  rw [hk_eq]
  have hk : my_pi (156420) = 14388 := pi_156420
  have hm0 : my_pi (437580) = 36764 := pi_437580
  have hm1_val : my_pi (438516) = 36825 := pi_438516
  rcases le_or_gt m 935 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 437580 := bound_le_helper m 935 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 936 ≤ m := hm_gt
    have h1 : 438516 ≤ m*(m+1)/2 := bound_gt_helper m 936 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_396 (m : ℕ) (hm1 : m ≥ 1) : my_pi (396*397) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 396*397 = 157212 := by decide
  rw [hk_eq]
  have hk : my_pi (157212) = 14453 := pi_157212
  have hm0 : my_pi (436645) = 36694 := pi_436645
  have hm1_val : my_pi (437580) = 36764 := pi_437580
  rcases le_or_gt m 934 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 436645 := bound_le_helper m 934 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 935 ≤ m := hm_gt
    have h1 : 437580 ≤ m*(m+1)/2 := bound_gt_helper m 935 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_397 (m : ℕ) (hm1 : m ≥ 1) : my_pi (397*398) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 397*398 = 158006 := by decide
  rw [hk_eq]
  have hk : my_pi (158006) = 14522 := pi_158006
  have hm0 : my_pi (435711) = 36625 := pi_435711
  have hm1_val : my_pi (436645) = 36694 := pi_436645
  rcases le_or_gt m 933 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 435711 := bound_le_helper m 933 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 934 ≤ m := hm_gt
    have h1 : 436645 ≤ m*(m+1)/2 := bound_gt_helper m 934 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_398 (m : ℕ) (hm1 : m ≥ 1) : my_pi (398*399) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 398*399 = 158802 := by decide
  rw [hk_eq]
  have hk : my_pi (158802) = 14585 := pi_158802
  have hm0 : my_pi (434778) = 36541 := pi_434778
  have hm1_val : my_pi (435711) = 36625 := pi_435711
  rcases le_or_gt m 932 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 434778 := bound_le_helper m 932 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 933 ≤ m := hm_gt
    have h1 : 435711 ≤ m*(m+1)/2 := bound_gt_helper m 933 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_399 (m : ℕ) (hm1 : m ≥ 1) : my_pi (399*400) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 399*400 = 159600 := by decide
  rw [hk_eq]
  have hk : my_pi (159600) = 14648 := pi_159600
  have hm0 : my_pi (433846) = 36470 := pi_433846
  have hm1_val : my_pi (434778) = 36541 := pi_434778
  rcases le_or_gt m 931 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 433846 := bound_le_helper m 931 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 932 ≤ m := hm_gt
    have h1 : 434778 ≤ m*(m+1)/2 := bound_gt_helper m 932 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_400 (m : ℕ) (hm1 : m ≥ 1) : my_pi (400*401) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 400*401 = 160400 := by decide
  rw [hk_eq]
  have hk : my_pi (160400) = 14716 := pi_160400
  have hm0 : my_pi (432915) = 36394 := pi_432915
  have hm1_val : my_pi (433846) = 36470 := pi_433846
  rcases le_or_gt m 930 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 432915 := bound_le_helper m 930 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 931 ≤ m := hm_gt
    have h1 : 433846 ≤ m*(m+1)/2 := bound_gt_helper m 931 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_401 (m : ℕ) (hm1 : m ≥ 1) : my_pi (401*402) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 401*402 = 161202 := by decide
  rw [hk_eq]
  have hk : my_pi (161202) = 14785 := pi_161202
  have hm0 : my_pi (431985) = 36316 := pi_431985
  have hm1_val : my_pi (432915) = 36394 := pi_432915
  rcases le_or_gt m 929 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 431985 := bound_le_helper m 929 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 930 ≤ m := hm_gt
    have h1 : 432915 ≤ m*(m+1)/2 := bound_gt_helper m 930 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_402 (m : ℕ) (hm1 : m ≥ 1) : my_pi (402*403) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 402*403 = 162006 := by decide
  rw [hk_eq]
  have hk : my_pi (162006) = 14852 := pi_162006
  have hm0 : my_pi (431056) = 36243 := pi_431056
  have hm1_val : my_pi (431985) = 36316 := pi_431985
  rcases le_or_gt m 928 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 431056 := bound_le_helper m 928 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 929 ≤ m := hm_gt
    have h1 : 431985 ≤ m*(m+1)/2 := bound_gt_helper m 929 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_403 (m : ℕ) (hm1 : m ≥ 1) : my_pi (403*404) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 403*404 = 162812 := by decide
  rw [hk_eq]
  have hk : my_pi (162812) = 14915 := pi_162812
  have hm0 : my_pi (430128) = 36172 := pi_430128
  have hm1_val : my_pi (431056) = 36243 := pi_431056
  rcases le_or_gt m 927 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 430128 := bound_le_helper m 927 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 928 ≤ m := hm_gt
    have h1 : 431056 ≤ m*(m+1)/2 := bound_gt_helper m 928 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_404 (m : ℕ) (hm1 : m ≥ 1) : my_pi (404*405) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 404*405 = 163620 := by decide
  rw [hk_eq]
  have hk : my_pi (163620) = 14981 := pi_163620
  have hm0 : my_pi (430128) = 36172 := pi_430128
  have hm1_val : my_pi (431056) = 36243 := pi_431056
  rcases le_or_gt m 927 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 430128 := bound_le_helper m 927 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 928 ≤ m := hm_gt
    have h1 : 431056 ≤ m*(m+1)/2 := bound_gt_helper m 928 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_405 (m : ℕ) (hm1 : m ≥ 1) : my_pi (405*406) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 405*406 = 164430 := by decide
  rw [hk_eq]
  have hk : my_pi (164430) = 15053 := pi_164430
  have hm0 : my_pi (429201) = 36086 := pi_429201
  have hm1_val : my_pi (430128) = 36172 := pi_430128
  rcases le_or_gt m 926 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 429201 := bound_le_helper m 926 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 927 ≤ m := hm_gt
    have h1 : 430128 ≤ m*(m+1)/2 := bound_gt_helper m 927 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_406 (m : ℕ) (hm1 : m ≥ 1) : my_pi (406*407) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 406*407 = 165242 := by decide
  rw [hk_eq]
  have hk : my_pi (165242) = 15111 := pi_165242
  have hm0 : my_pi (428275) = 36025 := pi_428275
  have hm1_val : my_pi (429201) = 36086 := pi_429201
  rcases le_or_gt m 925 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 428275 := bound_le_helper m 925 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 926 ≤ m := hm_gt
    have h1 : 429201 ≤ m*(m+1)/2 := bound_gt_helper m 926 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_407 (m : ℕ) (hm1 : m ≥ 1) : my_pi (407*408) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 407*408 = 166056 := by decide
  rw [hk_eq]
  have hk : my_pi (166056) = 15178 := pi_166056
  have hm0 : my_pi (427350) = 35950 := pi_427350
  have hm1_val : my_pi (428275) = 36025 := pi_428275
  rcases le_or_gt m 924 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 427350 := bound_le_helper m 924 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 925 ≤ m := hm_gt
    have h1 : 428275 ≤ m*(m+1)/2 := bound_gt_helper m 925 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_408 (m : ℕ) (hm1 : m ≥ 1) : my_pi (408*409) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 408*409 = 166872 := by decide
  rw [hk_eq]
  have hk : my_pi (166872) = 15246 := pi_166872
  have hm0 : my_pi (426426) = 35881 := pi_426426
  have hm1_val : my_pi (427350) = 35950 := pi_427350
  rcases le_or_gt m 923 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 426426 := bound_le_helper m 923 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 924 ≤ m := hm_gt
    have h1 : 427350 ≤ m*(m+1)/2 := bound_gt_helper m 924 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_409 (m : ℕ) (hm1 : m ≥ 1) : my_pi (409*410) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 409*410 = 167690 := by decide
  rw [hk_eq]
  have hk : my_pi (167690) = 15316 := pi_167690
  have hm0 : my_pi (425503) = 35819 := pi_425503
  have hm1_val : my_pi (426426) = 35881 := pi_426426
  rcases le_or_gt m 922 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 425503 := bound_le_helper m 922 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 923 ≤ m := hm_gt
    have h1 : 426426 ≤ m*(m+1)/2 := bound_gt_helper m 923 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_410 (m : ℕ) (hm1 : m ≥ 1) : my_pi (410*411) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 410*411 = 168510 := by decide
  rw [hk_eq]
  have hk : my_pi (168510) = 15375 := pi_168510
  have hm0 : my_pi (424581) = 35746 := pi_424581
  have hm1_val : my_pi (425503) = 35819 := pi_425503
  rcases le_or_gt m 921 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 424581 := bound_le_helper m 921 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 922 ≤ m := hm_gt
    have h1 : 425503 ≤ m*(m+1)/2 := bound_gt_helper m 922 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_411 (m : ℕ) (hm1 : m ≥ 1) : my_pi (411*412) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 411*412 = 169332 := by decide
  rw [hk_eq]
  have hk : my_pi (169332) = 15440 := pi_169332
  have hm0 : my_pi (423660) = 35672 := pi_423660
  have hm1_val : my_pi (424581) = 35746 := pi_424581
  rcases le_or_gt m 920 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 423660 := bound_le_helper m 920 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 921 ≤ m := hm_gt
    have h1 : 424581 ≤ m*(m+1)/2 := bound_gt_helper m 921 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_412 (m : ℕ) (hm1 : m ≥ 1) : my_pi (412*413) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 412*413 = 170156 := by decide
  rw [hk_eq]
  have hk : my_pi (170156) = 15509 := pi_170156
  have hm0 : my_pi (422740) = 35593 := pi_422740
  have hm1_val : my_pi (423660) = 35672 := pi_423660
  rcases le_or_gt m 919 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 422740 := bound_le_helper m 919 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 920 ≤ m := hm_gt
    have h1 : 423660 ≤ m*(m+1)/2 := bound_gt_helper m 920 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_413 (m : ℕ) (hm1 : m ≥ 1) : my_pi (413*414) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 413*414 = 170982 := by decide
  rw [hk_eq]
  have hk : my_pi (170982) = 15584 := pi_170982
  have hm0 : my_pi (421821) = 35529 := pi_421821
  have hm1_val : my_pi (422740) = 35593 := pi_422740
  rcases le_or_gt m 918 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 421821 := bound_le_helper m 918 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 919 ≤ m := hm_gt
    have h1 : 422740 ≤ m*(m+1)/2 := bound_gt_helper m 919 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_414 (m : ℕ) (hm1 : m ≥ 1) : my_pi (414*415) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 414*415 = 171810 := by decide
  rw [hk_eq]
  have hk : my_pi (171810) = 15651 := pi_171810
  have hm0 : my_pi (420903) = 35459 := pi_420903
  have hm1_val : my_pi (421821) = 35529 := pi_421821
  rcases le_or_gt m 917 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 420903 := bound_le_helper m 917 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 918 ≤ m := hm_gt
    have h1 : 421821 ≤ m*(m+1)/2 := bound_gt_helper m 918 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_415 (m : ℕ) (hm1 : m ≥ 1) : my_pi (415*416) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 415*416 = 172640 := by decide
  rw [hk_eq]
  have hk : my_pi (172640) = 15723 := pi_172640
  have hm0 : my_pi (419986) = 35389 := pi_419986
  have hm1_val : my_pi (420903) = 35459 := pi_420903
  rcases le_or_gt m 916 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 419986 := bound_le_helper m 916 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 917 ≤ m := hm_gt
    have h1 : 420903 ≤ m*(m+1)/2 := bound_gt_helper m 917 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_416 (m : ℕ) (hm1 : m ≥ 1) : my_pi (416*417) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 416*417 = 173472 := by decide
  rw [hk_eq]
  have hk : my_pi (173472) = 15785 := pi_173472
  have hm0 : my_pi (419070) = 35320 := pi_419070
  have hm1_val : my_pi (419986) = 35389 := pi_419986
  rcases le_or_gt m 915 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 419070 := bound_le_helper m 915 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 916 ≤ m := hm_gt
    have h1 : 419986 ≤ m*(m+1)/2 := bound_gt_helper m 916 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_417 (m : ℕ) (hm1 : m ≥ 1) : my_pi (417*418) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 417*418 = 174306 := by decide
  rw [hk_eq]
  have hk : my_pi (174306) = 15860 := pi_174306
  have hm0 : my_pi (418155) = 35242 := pi_418155
  have hm1_val : my_pi (419070) = 35320 := pi_419070
  rcases le_or_gt m 914 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 418155 := bound_le_helper m 914 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 915 ≤ m := hm_gt
    have h1 : 419070 ≤ m*(m+1)/2 := bound_gt_helper m 915 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_418 (m : ℕ) (hm1 : m ≥ 1) : my_pi (418*419) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 418*419 = 175142 := by decide
  rw [hk_eq]
  have hk : my_pi (175142) = 15927 := pi_175142
  have hm0 : my_pi (417241) = 35169 := pi_417241
  have hm1_val : my_pi (418155) = 35242 := pi_418155
  rcases le_or_gt m 913 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 417241 := bound_le_helper m 913 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 914 ≤ m := hm_gt
    have h1 : 418155 ≤ m*(m+1)/2 := bound_gt_helper m 914 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_419 (m : ℕ) (hm1 : m ≥ 1) : my_pi (419*420) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 419*420 = 175980 := by decide
  rw [hk_eq]
  have hk : my_pi (175980) = 15989 := pi_175980
  have hm0 : my_pi (416328) = 35101 := pi_416328
  have hm1_val : my_pi (417241) = 35169 := pi_417241
  rcases le_or_gt m 912 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 416328 := bound_le_helper m 912 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 913 ≤ m := hm_gt
    have h1 : 417241 ≤ m*(m+1)/2 := bound_gt_helper m 913 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_420 (m : ℕ) (hm1 : m ≥ 1) : my_pi (420*421) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 420*421 = 176820 := by decide
  rw [hk_eq]
  have hk : my_pi (176820) = 16073 := pi_176820
  have hm0 : my_pi (415416) = 35031 := pi_415416
  have hm1_val : my_pi (416328) = 35101 := pi_416328
  rcases le_or_gt m 911 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 415416 := bound_le_helper m 911 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 912 ≤ m := hm_gt
    have h1 : 416328 ≤ m*(m+1)/2 := bound_gt_helper m 912 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_421 (m : ℕ) (hm1 : m ≥ 1) : my_pi (421*422) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 421*422 = 177662 := by decide
  rw [hk_eq]
  have hk : my_pi (177662) = 16132 := pi_177662
  have hm0 : my_pi (414505) = 34956 := pi_414505
  have hm1_val : my_pi (415416) = 35031 := pi_415416
  rcases le_or_gt m 910 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 414505 := bound_le_helper m 910 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 911 ≤ m := hm_gt
    have h1 : 415416 ≤ m*(m+1)/2 := bound_gt_helper m 911 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_422 (m : ℕ) (hm1 : m ≥ 1) : my_pi (422*423) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 422*423 = 178506 := by decide
  rw [hk_eq]
  have hk : my_pi (178506) = 16202 := pi_178506
  have hm0 : my_pi (413595) = 34885 := pi_413595
  have hm1_val : my_pi (414505) = 34956 := pi_414505
  rcases le_or_gt m 909 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 413595 := bound_le_helper m 909 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 910 ≤ m := hm_gt
    have h1 : 414505 ≤ m*(m+1)/2 := bound_gt_helper m 910 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_423 (m : ℕ) (hm1 : m ≥ 1) : my_pi (423*424) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 423*424 = 179352 := by decide
  rw [hk_eq]
  have hk : my_pi (179352) = 16277 := pi_179352
  have hm0 : my_pi (412686) = 34826 := pi_412686
  have hm1_val : my_pi (413595) = 34885 := pi_413595
  rcases le_or_gt m 908 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 412686 := bound_le_helper m 908 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 909 ≤ m := hm_gt
    have h1 : 413595 ≤ m*(m+1)/2 := bound_gt_helper m 909 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_424 (m : ℕ) (hm1 : m ≥ 1) : my_pi (424*425) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 424*425 = 180200 := by decide
  rw [hk_eq]
  have hk : my_pi (180200) = 16355 := pi_180200
  have hm0 : my_pi (411778) = 34753 := pi_411778
  have hm1_val : my_pi (412686) = 34826 := pi_412686
  rcases le_or_gt m 907 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 411778 := bound_le_helper m 907 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 908 ≤ m := hm_gt
    have h1 : 412686 ≤ m*(m+1)/2 := bound_gt_helper m 908 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_425 (m : ℕ) (hm1 : m ≥ 1) : my_pi (425*426) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 425*426 = 181050 := by decide
  rw [hk_eq]
  have hk : my_pi (181050) = 16418 := pi_181050
  have hm0 : my_pi (410871) = 34681 := pi_410871
  have hm1_val : my_pi (411778) = 34753 := pi_411778
  rcases le_or_gt m 906 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 410871 := bound_le_helper m 906 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 907 ≤ m := hm_gt
    have h1 : 411778 ≤ m*(m+1)/2 := bound_gt_helper m 907 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_426 (m : ℕ) (hm1 : m ≥ 1) : my_pi (426*427) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 426*427 = 181902 := by decide
  rw [hk_eq]
  have hk : my_pi (181902) = 16482 := pi_181902
  have hm0 : my_pi (409965) = 34610 := pi_409965
  have hm1_val : my_pi (410871) = 34681 := pi_410871
  rcases le_or_gt m 905 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 409965 := bound_le_helper m 905 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 906 ≤ m := hm_gt
    have h1 : 410871 ≤ m*(m+1)/2 := bound_gt_helper m 906 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_427 (m : ℕ) (hm1 : m ≥ 1) : my_pi (427*428) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 427*428 = 182756 := by decide
  rw [hk_eq]
  have hk : my_pi (182756) = 16561 := pi_182756
  have hm0 : my_pi (409060) = 34537 := pi_409060
  have hm1_val : my_pi (409965) = 34610 := pi_409965
  rcases le_or_gt m 904 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 409060 := bound_le_helper m 904 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 905 ≤ m := hm_gt
    have h1 : 409965 ≤ m*(m+1)/2 := bound_gt_helper m 905 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_428 (m : ℕ) (hm1 : m ≥ 1) : my_pi (428*429) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 428*429 = 183612 := by decide
  rw [hk_eq]
  have hk : my_pi (183612) = 16636 := pi_183612
  have hm0 : my_pi (408156) = 34463 := pi_408156
  have hm1_val : my_pi (409060) = 34537 := pi_409060
  rcases le_or_gt m 903 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 408156 := bound_le_helper m 903 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 904 ≤ m := hm_gt
    have h1 : 409060 ≤ m*(m+1)/2 := bound_gt_helper m 904 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_429 (m : ℕ) (hm1 : m ≥ 1) : my_pi (429*430) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 429*430 = 184470 := by decide
  rw [hk_eq]
  have hk : my_pi (184470) = 16700 := pi_184470
  have hm0 : my_pi (407253) = 34389 := pi_407253
  have hm1_val : my_pi (408156) = 34463 := pi_408156
  rcases le_or_gt m 902 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 407253 := bound_le_helper m 902 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 903 ≤ m := hm_gt
    have h1 : 408156 ≤ m*(m+1)/2 := bound_gt_helper m 903 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_430 (m : ℕ) (hm1 : m ≥ 1) : my_pi (430*431) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 430*431 = 185330 := by decide
  rw [hk_eq]
  have hk : my_pi (185330) = 16775 := pi_185330
  have hm0 : my_pi (406351) = 34328 := pi_406351
  have hm1_val : my_pi (407253) = 34389 := pi_407253
  rcases le_or_gt m 901 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 406351 := bound_le_helper m 901 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 902 ≤ m := hm_gt
    have h1 : 407253 ≤ m*(m+1)/2 := bound_gt_helper m 902 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_431 (m : ℕ) (hm1 : m ≥ 1) : my_pi (431*432) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 431*432 = 186192 := by decide
  rw [hk_eq]
  have hk : my_pi (186192) = 16855 := pi_186192
  have hm0 : my_pi (405450) = 34257 := pi_405450
  have hm1_val : my_pi (406351) = 34328 := pi_406351
  rcases le_or_gt m 900 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 405450 := bound_le_helper m 900 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 901 ≤ m := hm_gt
    have h1 : 406351 ≤ m*(m+1)/2 := bound_gt_helper m 901 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_432 (m : ℕ) (hm1 : m ≥ 1) : my_pi (432*433) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 432*433 = 187056 := by decide
  rw [hk_eq]
  have hk : my_pi (187056) = 16920 := pi_187056
  have hm0 : my_pi (404550) = 34200 := pi_404550
  have hm1_val : my_pi (405450) = 34257 := pi_405450
  rcases le_or_gt m 899 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 404550 := bound_le_helper m 899 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 900 ≤ m := hm_gt
    have h1 : 405450 ≤ m*(m+1)/2 := bound_gt_helper m 900 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_433 (m : ℕ) (hm1 : m ≥ 1) : my_pi (433*434) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 433*434 = 187922 := by decide
  rw [hk_eq]
  have hk : my_pi (187922) = 16996 := pi_187922
  have hm0 : my_pi (403651) = 34125 := pi_403651
  have hm1_val : my_pi (404550) = 34200 := pi_404550
  rcases le_or_gt m 898 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 403651 := bound_le_helper m 898 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 899 ≤ m := hm_gt
    have h1 : 404550 ≤ m*(m+1)/2 := bound_gt_helper m 899 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_434 (m : ℕ) (hm1 : m ≥ 1) : my_pi (434*435) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 434*435 = 188790 := by decide
  rw [hk_eq]
  have hk : my_pi (188790) = 17062 := pi_188790
  have hm0 : my_pi (402753) = 34057 := pi_402753
  have hm1_val : my_pi (403651) = 34125 := pi_403651
  rcases le_or_gt m 897 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 402753 := bound_le_helper m 897 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 898 ≤ m := hm_gt
    have h1 : 403651 ≤ m*(m+1)/2 := bound_gt_helper m 898 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_435 (m : ℕ) (hm1 : m ≥ 1) : my_pi (435*436) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 435*436 = 189660 := by decide
  rw [hk_eq]
  have hk : my_pi (189660) = 17139 := pi_189660
  have hm0 : my_pi (401856) = 33988 := pi_401856
  have hm1_val : my_pi (402753) = 34057 := pi_402753
  rcases le_or_gt m 896 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 401856 := bound_le_helper m 896 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 897 ≤ m := hm_gt
    have h1 : 402753 ≤ m*(m+1)/2 := bound_gt_helper m 897 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_436 (m : ℕ) (hm1 : m ≥ 1) : my_pi (436*437) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 436*437 = 190532 := by decide
  rw [hk_eq]
  have hk : my_pi (190532) = 17204 := pi_190532
  have hm0 : my_pi (400960) = 33928 := pi_400960
  have hm1_val : my_pi (401856) = 33988 := pi_401856
  rcases le_or_gt m 895 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 400960 := bound_le_helper m 895 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 896 ≤ m := hm_gt
    have h1 : 401856 ≤ m*(m+1)/2 := bound_gt_helper m 896 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_437 (m : ℕ) (hm1 : m ≥ 1) : my_pi (437*438) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 437*438 = 191406 := by decide
  rw [hk_eq]
  have hk : my_pi (191406) = 17273 := pi_191406
  have hm0 : my_pi (400065) = 33864 := pi_400065
  have hm1_val : my_pi (400960) = 33928 := pi_400960
  rcases le_or_gt m 894 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 400065 := bound_le_helper m 894 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 895 ≤ m := hm_gt
    have h1 : 400960 ≤ m*(m+1)/2 := bound_gt_helper m 895 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_438 (m : ℕ) (hm1 : m ≥ 1) : my_pi (438*439) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 438*439 = 192282 := by decide
  rw [hk_eq]
  have hk : my_pi (192282) = 17352 := pi_192282
  have hm0 : my_pi (399171) = 33794 := pi_399171
  have hm1_val : my_pi (400065) = 33864 := pi_400065
  rcases le_or_gt m 893 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 399171 := bound_le_helper m 893 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 894 ≤ m := hm_gt
    have h1 : 400065 ≤ m*(m+1)/2 := bound_gt_helper m 894 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_439 (m : ℕ) (hm1 : m ≥ 1) : my_pi (439*440) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 439*440 = 193160 := by decide
  rw [hk_eq]
  have hk : my_pi (193160) = 17428 := pi_193160
  have hm0 : my_pi (398278) = 33722 := pi_398278
  have hm1_val : my_pi (399171) = 33794 := pi_399171
  rcases le_or_gt m 892 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 398278 := bound_le_helper m 892 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 893 ≤ m := hm_gt
    have h1 : 399171 ≤ m*(m+1)/2 := bound_gt_helper m 893 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_440 (m : ℕ) (hm1 : m ≥ 1) : my_pi (440*441) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 440*441 = 194040 := by decide
  rw [hk_eq]
  have hk : my_pi (194040) = 17502 := pi_194040
  have hm0 : my_pi (397386) = 33653 := pi_397386
  have hm1_val : my_pi (398278) = 33722 := pi_398278
  rcases le_or_gt m 891 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 397386 := bound_le_helper m 891 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 892 ≤ m := hm_gt
    have h1 : 398278 ≤ m*(m+1)/2 := bound_gt_helper m 892 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_441 (m : ℕ) (hm1 : m ≥ 1) : my_pi (441*442) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 441*442 = 194922 := by decide
  rw [hk_eq]
  have hk : my_pi (194922) = 17568 := pi_194922
  have hm0 : my_pi (396495) = 33585 := pi_396495
  have hm1_val : my_pi (397386) = 33653 := pi_397386
  rcases le_or_gt m 890 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 396495 := bound_le_helper m 890 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 891 ≤ m := hm_gt
    have h1 : 397386 ≤ m*(m+1)/2 := bound_gt_helper m 891 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_442 (m : ℕ) (hm1 : m ≥ 1) : my_pi (442*443) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 442*443 = 195806 := by decide
  rw [hk_eq]
  have hk : my_pi (195806) = 17640 := pi_195806
  have hm0 : my_pi (394716) = 33449 := pi_394716
  have hm1_val : my_pi (395605) = 33522 := pi_395605
  rcases le_or_gt m 888 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 394716 := bound_le_helper m 888 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 889 ≤ m := hm_gt
    have h1 : 395605 ≤ m*(m+1)/2 := bound_gt_helper m 889 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_443 (m : ℕ) (hm1 : m ≥ 1) : my_pi (443*444) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 443*444 = 196692 := by decide
  rw [hk_eq]
  have hk : my_pi (196692) = 17711 := pi_196692
  have hm0 : my_pi (393828) = 33385 := pi_393828
  have hm1_val : my_pi (394716) = 33449 := pi_394716
  rcases le_or_gt m 887 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 393828 := bound_le_helper m 887 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 888 ≤ m := hm_gt
    have h1 : 394716 ≤ m*(m+1)/2 := bound_gt_helper m 888 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_444 (m : ℕ) (hm1 : m ≥ 1) : my_pi (444*445) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 444*445 = 197580 := by decide
  rw [hk_eq]
  have hk : my_pi (197580) = 17785 := pi_197580
  have hm0 : my_pi (392941) = 33308 := pi_392941
  have hm1_val : my_pi (393828) = 33385 := pi_393828
  rcases le_or_gt m 886 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 392941 := bound_le_helper m 886 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 887 ≤ m := hm_gt
    have h1 : 393828 ≤ m*(m+1)/2 := bound_gt_helper m 887 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_445 (m : ℕ) (hm1 : m ≥ 1) : my_pi (445*446) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 445*446 = 198470 := by decide
  rw [hk_eq]
  have hk : my_pi (198470) = 17862 := pi_198470
  have hm0 : my_pi (392055) = 33230 := pi_392055
  have hm1_val : my_pi (392941) = 33308 := pi_392941
  rcases le_or_gt m 885 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 392055 := bound_le_helper m 885 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 886 ≤ m := hm_gt
    have h1 : 392941 ≤ m*(m+1)/2 := bound_gt_helper m 886 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_446 (m : ℕ) (hm1 : m ≥ 1) : my_pi (446*447) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 446*447 = 199362 := by decide
  rw [hk_eq]
  have hk : my_pi (199362) = 17930 := pi_199362
  have hm0 : my_pi (391170) = 33163 := pi_391170
  have hm1_val : my_pi (392055) = 33230 := pi_392055
  rcases le_or_gt m 884 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 391170 := bound_le_helper m 884 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 885 ≤ m := hm_gt
    have h1 : 392055 ≤ m*(m+1)/2 := bound_gt_helper m 885 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_447 (m : ℕ) (hm1 : m ≥ 1) : my_pi (447*448) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 447*448 = 200256 := by decide
  rw [hk_eq]
  have hk : my_pi (200256) = 18005 := pi_200256
  have hm0 : my_pi (390286) = 33089 := pi_390286
  have hm1_val : my_pi (391170) = 33163 := pi_391170
  rcases le_or_gt m 883 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 390286 := bound_le_helper m 883 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 884 ≤ m := hm_gt
    have h1 : 391170 ≤ m*(m+1)/2 := bound_gt_helper m 884 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_448 (m : ℕ) (hm1 : m ≥ 1) : my_pi (448*449) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 448*449 = 201152 := by decide
  rw [hk_eq]
  have hk : my_pi (201152) = 18073 := pi_201152
  have hm0 : my_pi (389403) = 33016 := pi_389403
  have hm1_val : my_pi (390286) = 33089 := pi_390286
  rcases le_or_gt m 882 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 389403 := bound_le_helper m 882 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 883 ≤ m := hm_gt
    have h1 : 390286 ≤ m*(m+1)/2 := bound_gt_helper m 883 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_449 (m : ℕ) (hm1 : m ≥ 1) : my_pi (449*450) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 449*450 = 202050 := by decide
  rw [hk_eq]
  have hk : my_pi (202050) = 18152 := pi_202050
  have hm0 : my_pi (388521) = 32949 := pi_388521
  have hm1_val : my_pi (389403) = 33016 := pi_389403
  rcases le_or_gt m 881 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 388521 := bound_le_helper m 881 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 882 ≤ m := hm_gt
    have h1 : 389403 ≤ m*(m+1)/2 := bound_gt_helper m 882 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_450 (m : ℕ) (hm1 : m ≥ 1) : my_pi (450*451) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 450*451 = 202950 := by decide
  rw [hk_eq]
  have hk : my_pi (202950) = 18221 := pi_202950
  have hm0 : my_pi (387640) = 32883 := pi_387640
  have hm1_val : my_pi (388521) = 32949 := pi_388521
  rcases le_or_gt m 880 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 387640 := bound_le_helper m 880 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 881 ≤ m := hm_gt
    have h1 : 388521 ≤ m*(m+1)/2 := bound_gt_helper m 881 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_451 (m : ℕ) (hm1 : m ≥ 1) : my_pi (451*452) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 451*452 = 203852 := by decide
  rw [hk_eq]
  have hk : my_pi (203852) = 18290 := pi_203852
  have hm0 : my_pi (386760) = 32826 := pi_386760
  have hm1_val : my_pi (387640) = 32883 := pi_387640
  rcases le_or_gt m 879 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 386760 := bound_le_helper m 879 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 880 ≤ m := hm_gt
    have h1 : 387640 ≤ m*(m+1)/2 := bound_gt_helper m 880 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_452 (m : ℕ) (hm1 : m ≥ 1) : my_pi (452*453) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 452*453 = 204756 := by decide
  rw [hk_eq]
  have hk : my_pi (204756) = 18363 := pi_204756
  have hm0 : my_pi (385881) = 32752 := pi_385881
  have hm1_val : my_pi (386760) = 32826 := pi_386760
  rcases le_or_gt m 878 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 385881 := bound_le_helper m 878 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 879 ≤ m := hm_gt
    have h1 : 386760 ≤ m*(m+1)/2 := bound_gt_helper m 879 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_453 (m : ℕ) (hm1 : m ≥ 1) : my_pi (453*454) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 453*454 = 205662 := by decide
  rw [hk_eq]
  have hk : my_pi (205662) = 18442 := pi_205662
  have hm0 : my_pi (385003) = 32682 := pi_385003
  have hm1_val : my_pi (385881) = 32752 := pi_385881
  rcases le_or_gt m 877 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 385003 := bound_le_helper m 877 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 878 ≤ m := hm_gt
    have h1 : 385881 ≤ m*(m+1)/2 := bound_gt_helper m 878 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_454 (m : ℕ) (hm1 : m ≥ 1) : my_pi (454*455) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 454*455 = 206570 := by decide
  rw [hk_eq]
  have hk : my_pi (206570) = 18517 := pi_206570
  have hm0 : my_pi (384126) = 32613 := pi_384126
  have hm1_val : my_pi (385003) = 32682 := pi_385003
  rcases le_or_gt m 876 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 384126 := bound_le_helper m 876 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 877 ≤ m := hm_gt
    have h1 : 385003 ≤ m*(m+1)/2 := bound_gt_helper m 877 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_455 (m : ℕ) (hm1 : m ≥ 1) : my_pi (455*456) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 455*456 = 207480 := by decide
  rw [hk_eq]
  have hk : my_pi (207480) = 18588 := pi_207480
  have hm0 : my_pi (383250) = 32542 := pi_383250
  have hm1_val : my_pi (384126) = 32613 := pi_384126
  rcases le_or_gt m 875 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 383250 := bound_le_helper m 875 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 876 ≤ m := hm_gt
    have h1 : 384126 ≤ m*(m+1)/2 := bound_gt_helper m 876 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_456 (m : ℕ) (hm1 : m ≥ 1) : my_pi (456*457) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 456*457 = 208392 := by decide
  rw [hk_eq]
  have hk : my_pi (208392) = 18669 := pi_208392
  have hm0 : my_pi (382375) = 32473 := pi_382375
  have hm1_val : my_pi (383250) = 32542 := pi_383250
  rcases le_or_gt m 874 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 382375 := bound_le_helper m 874 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 875 ≤ m := hm_gt
    have h1 : 383250 ≤ m*(m+1)/2 := bound_gt_helper m 875 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_457 (m : ℕ) (hm1 : m ≥ 1) : my_pi (457*458) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 457*458 = 209306 := by decide
  rw [hk_eq]
  have hk : my_pi (209306) = 18743 := pi_209306
  have hm0 : my_pi (381501) = 32412 := pi_381501
  have hm1_val : my_pi (382375) = 32473 := pi_382375
  rcases le_or_gt m 873 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 381501 := bound_le_helper m 873 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 874 ≤ m := hm_gt
    have h1 : 382375 ≤ m*(m+1)/2 := bound_gt_helper m 874 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_458 (m : ℕ) (hm1 : m ≥ 1) : my_pi (458*459) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 458*459 = 210222 := by decide
  rw [hk_eq]
  have hk : my_pi (210222) = 18828 := pi_210222
  have hm0 : my_pi (379756) = 32280 := pi_379756
  have hm1_val : my_pi (380628) = 32345 := pi_380628
  rcases le_or_gt m 871 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 379756 := bound_le_helper m 871 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 872 ≤ m := hm_gt
    have h1 : 380628 ≤ m*(m+1)/2 := bound_gt_helper m 872 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_459 (m : ℕ) (hm1 : m ≥ 1) : my_pi (459*460) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 459*460 = 211140 := by decide
  rw [hk_eq]
  have hk : my_pi (211140) = 18902 := pi_211140
  have hm0 : my_pi (378885) = 32207 := pi_378885
  have hm1_val : my_pi (379756) = 32280 := pi_379756
  rcases le_or_gt m 870 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 378885 := bound_le_helper m 870 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 871 ≤ m := hm_gt
    have h1 : 379756 ≤ m*(m+1)/2 := bound_gt_helper m 871 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_460 (m : ℕ) (hm1 : m ≥ 1) : my_pi (460*461) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 460*461 = 212060 := by decide
  rw [hk_eq]
  have hk : my_pi (212060) = 18980 := pi_212060
  have hm0 : my_pi (378015) = 32141 := pi_378015
  have hm1_val : my_pi (378885) = 32207 := pi_378885
  rcases le_or_gt m 869 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 378015 := bound_le_helper m 869 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 870 ≤ m := hm_gt
    have h1 : 378885 ≤ m*(m+1)/2 := bound_gt_helper m 870 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_461 (m : ℕ) (hm1 : m ≥ 1) : my_pi (461*462) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 461*462 = 212982 := by decide
  rw [hk_eq]
  have hk : my_pi (212982) = 19044 := pi_212982
  have hm0 : my_pi (377146) = 32078 := pi_377146
  have hm1_val : my_pi (378015) = 32141 := pi_378015
  rcases le_or_gt m 868 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 377146 := bound_le_helper m 868 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 869 ≤ m := hm_gt
    have h1 : 378015 ≤ m*(m+1)/2 := bound_gt_helper m 869 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_462 (m : ℕ) (hm1 : m ≥ 1) : my_pi (462*463) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 462*463 = 213906 := by decide
  rw [hk_eq]
  have hk : my_pi (213906) = 19118 := pi_213906
  have hm0 : my_pi (376278) = 32009 := pi_376278
  have hm1_val : my_pi (377146) = 32078 := pi_377146
  rcases le_or_gt m 867 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 376278 := bound_le_helper m 867 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 868 ≤ m := hm_gt
    have h1 : 377146 ≤ m*(m+1)/2 := bound_gt_helper m 868 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_463 (m : ℕ) (hm1 : m ≥ 1) : my_pi (463*464) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 463*464 = 214832 := by decide
  rw [hk_eq]
  have hk : my_pi (214832) = 19202 := pi_214832
  have hm0 : my_pi (375411) = 31943 := pi_375411
  have hm1_val : my_pi (376278) = 32009 := pi_376278
  rcases le_or_gt m 866 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 375411 := bound_le_helper m 866 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 867 ≤ m := hm_gt
    have h1 : 376278 ≤ m*(m+1)/2 := bound_gt_helper m 867 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_464 (m : ℕ) (hm1 : m ≥ 1) : my_pi (464*465) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 464*465 = 215760 := by decide
  rw [hk_eq]
  have hk : my_pi (215760) = 19267 := pi_215760
  have hm0 : my_pi (374545) = 31864 := pi_374545
  have hm1_val : my_pi (375411) = 31943 := pi_375411
  rcases le_or_gt m 865 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 374545 := bound_le_helper m 865 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 866 ≤ m := hm_gt
    have h1 : 375411 ≤ m*(m+1)/2 := bound_gt_helper m 866 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_465 (m : ℕ) (hm1 : m ≥ 1) : my_pi (465*466) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 465*466 = 216690 := by decide
  rw [hk_eq]
  have hk : my_pi (216690) = 19337 := pi_216690
  have hm0 : my_pi (373680) = 31801 := pi_373680
  have hm1_val : my_pi (374545) = 31864 := pi_374545
  rcases le_or_gt m 864 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 373680 := bound_le_helper m 864 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 865 ≤ m := hm_gt
    have h1 : 374545 ≤ m*(m+1)/2 := bound_gt_helper m 865 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_466 (m : ℕ) (hm1 : m ≥ 1) : my_pi (466*467) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 466*467 = 217622 := by decide
  rw [hk_eq]
  have hk : my_pi (217622) = 19416 := pi_217622
  have hm0 : my_pi (372816) = 31733 := pi_372816
  have hm1_val : my_pi (373680) = 31801 := pi_373680
  rcases le_or_gt m 863 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 372816 := bound_le_helper m 863 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 864 ≤ m := hm_gt
    have h1 : 373680 ≤ m*(m+1)/2 := bound_gt_helper m 864 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_467 (m : ℕ) (hm1 : m ≥ 1) : my_pi (467*468) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 467*468 = 218556 := by decide
  rw [hk_eq]
  have hk : my_pi (218556) = 19488 := pi_218556
  have hm0 : my_pi (371953) = 31664 := pi_371953
  have hm1_val : my_pi (372816) = 31733 := pi_372816
  rcases le_or_gt m 862 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 371953 := bound_le_helper m 862 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 863 ≤ m := hm_gt
    have h1 : 372816 ≤ m*(m+1)/2 := bound_gt_helper m 863 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_468 (m : ℕ) (hm1 : m ≥ 1) : my_pi (468*469) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 468*469 = 219492 := by decide
  rw [hk_eq]
  have hk : my_pi (219492) = 19566 := pi_219492
  have hm0 : my_pi (370230) = 31542 := pi_370230
  have hm1_val : my_pi (371091) = 31599 := pi_371091
  rcases le_or_gt m 860 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 370230 := bound_le_helper m 860 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 861 ≤ m := hm_gt
    have h1 : 371091 ≤ m*(m+1)/2 := bound_gt_helper m 861 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_469 (m : ℕ) (hm1 : m ≥ 1) : my_pi (469*470) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 469*470 = 220430 := by decide
  rw [hk_eq]
  have hk : my_pi (220430) = 19650 := pi_220430
  have hm0 : my_pi (369370) = 31483 := pi_369370
  have hm1_val : my_pi (370230) = 31542 := pi_370230
  rcases le_or_gt m 859 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 369370 := bound_le_helper m 859 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 860 ≤ m := hm_gt
    have h1 : 370230 ≤ m*(m+1)/2 := bound_gt_helper m 860 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_470 (m : ℕ) (hm1 : m ≥ 1) : my_pi (470*471) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 470*471 = 221370 := by decide
  rw [hk_eq]
  have hk : my_pi (221370) = 19724 := pi_221370
  have hm0 : my_pi (368511) = 31421 := pi_368511
  have hm1_val : my_pi (369370) = 31483 := pi_369370
  rcases le_or_gt m 858 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 368511 := bound_le_helper m 858 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 859 ≤ m := hm_gt
    have h1 : 369370 ≤ m*(m+1)/2 := bound_gt_helper m 859 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_471 (m : ℕ) (hm1 : m ≥ 1) : my_pi (471*472) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 471*472 = 222312 := by decide
  rw [hk_eq]
  have hk : my_pi (222312) = 19802 := pi_222312
  have hm0 : my_pi (366796) = 31284 := pi_366796
  have hm1_val : my_pi (367653) = 31356 := pi_367653
  rcases le_or_gt m 856 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 366796 := bound_le_helper m 856 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 857 ≤ m := hm_gt
    have h1 : 367653 ≤ m*(m+1)/2 := bound_gt_helper m 857 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_472 (m : ℕ) (hm1 : m ≥ 1) : my_pi (472*473) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 472*473 = 223256 := by decide
  rw [hk_eq]
  have hk : my_pi (223256) = 19880 := pi_223256
  have hm0 : my_pi (365940) = 31215 := pi_365940
  have hm1_val : my_pi (366796) = 31284 := pi_366796
  rcases le_or_gt m 855 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 365940 := bound_le_helper m 855 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 856 ≤ m := hm_gt
    have h1 : 366796 ≤ m*(m+1)/2 := bound_gt_helper m 856 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_473 (m : ℕ) (hm1 : m ≥ 1) : my_pi (473*474) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 473*474 = 224202 := by decide
  rw [hk_eq]
  have hk : my_pi (224202) = 19955 := pi_224202
  have hm0 : my_pi (365085) = 31147 := pi_365085
  have hm1_val : my_pi (365940) = 31215 := pi_365940
  rcases le_or_gt m 854 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 365085 := bound_le_helper m 854 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 855 ≤ m := hm_gt
    have h1 : 365940 ≤ m*(m+1)/2 := bound_gt_helper m 855 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_474 (m : ℕ) (hm1 : m ≥ 1) : my_pi (474*475) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 474*475 = 225150 := by decide
  rw [hk_eq]
  have hk : my_pi (225150) = 20032 := pi_225150
  have hm0 : my_pi (364231) = 31079 := pi_364231
  have hm1_val : my_pi (365085) = 31147 := pi_365085
  rcases le_or_gt m 853 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 364231 := bound_le_helper m 853 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 854 ≤ m := hm_gt
    have h1 : 365085 ≤ m*(m+1)/2 := bound_gt_helper m 854 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_475 (m : ℕ) (hm1 : m ≥ 1) : my_pi (475*476) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 475*476 = 226100 := by decide
  rw [hk_eq]
  have hk : my_pi (226100) = 20111 := pi_226100
  have hm0 : my_pi (363378) = 31011 := pi_363378
  have hm1_val : my_pi (364231) = 31079 := pi_364231
  rcases le_or_gt m 852 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 363378 := bound_le_helper m 852 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 853 ≤ m := hm_gt
    have h1 : 364231 ≤ m*(m+1)/2 := bound_gt_helper m 853 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_476 (m : ℕ) (hm1 : m ≥ 1) : my_pi (476*477) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 476*477 = 227052 := by decide
  rw [hk_eq]
  have hk : my_pi (227052) = 20182 := pi_227052
  have hm0 : my_pi (362526) = 30949 := pi_362526
  have hm1_val : my_pi (363378) = 31011 := pi_363378
  rcases le_or_gt m 851 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 362526 := bound_le_helper m 851 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 852 ≤ m := hm_gt
    have h1 : 363378 ≤ m*(m+1)/2 := bound_gt_helper m 852 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_477 (m : ℕ) (hm1 : m ≥ 1) : my_pi (477*478) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 477*478 = 228006 := by decide
  rw [hk_eq]
  have hk : my_pi (228006) = 20260 := pi_228006
  have hm0 : my_pi (361675) = 30877 := pi_361675
  have hm1_val : my_pi (362526) = 30949 := pi_362526
  rcases le_or_gt m 850 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 361675 := bound_le_helper m 850 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 851 ≤ m := hm_gt
    have h1 : 362526 ≤ m*(m+1)/2 := bound_gt_helper m 851 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_478 (m : ℕ) (hm1 : m ≥ 1) : my_pi (478*479) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 478*479 = 228962 := by decide
  rw [hk_eq]
  have hk : my_pi (228962) = 20347 := pi_228962
  have hm0 : my_pi (359976) = 30755 := pi_359976
  have hm1_val : my_pi (360825) = 30810 := pi_360825
  rcases le_or_gt m 848 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 359976 := bound_le_helper m 848 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 849 ≤ m := hm_gt
    have h1 : 360825 ≤ m*(m+1)/2 := bound_gt_helper m 849 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_479 (m : ℕ) (hm1 : m ≥ 1) : my_pi (479*480) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 479*480 = 229920 := by decide
  rw [hk_eq]
  have hk : my_pi (229920) = 20430 := pi_229920
  have hm0 : my_pi (359128) = 30694 := pi_359128
  have hm1_val : my_pi (359976) = 30755 := pi_359976
  rcases le_or_gt m 847 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 359128 := bound_le_helper m 847 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 848 ≤ m := hm_gt
    have h1 : 359976 ≤ m*(m+1)/2 := bound_gt_helper m 848 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_480 (m : ℕ) (hm1 : m ≥ 1) : my_pi (480*481) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 480*481 = 230880 := by decide
  rw [hk_eq]
  have hk : my_pi (230880) = 20512 := pi_230880
  have hm0 : my_pi (358281) = 30623 := pi_358281
  have hm1_val : my_pi (359128) = 30694 := pi_359128
  rcases le_or_gt m 846 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 358281 := bound_le_helper m 846 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 847 ≤ m := hm_gt
    have h1 : 359128 ≤ m*(m+1)/2 := bound_gt_helper m 847 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_481 (m : ℕ) (hm1 : m ≥ 1) : my_pi (481*482) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 481*482 = 231842 := by decide
  rw [hk_eq]
  have hk : my_pi (231842) = 20588 := pi_231842
  have hm0 : my_pi (357435) = 30555 := pi_357435
  have hm1_val : my_pi (358281) = 30623 := pi_358281
  rcases le_or_gt m 845 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 357435 := bound_le_helper m 845 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 846 ≤ m := hm_gt
    have h1 : 358281 ≤ m*(m+1)/2 := bound_gt_helper m 846 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_482 (m : ℕ) (hm1 : m ≥ 1) : my_pi (482*483) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 482*483 = 232806 := by decide
  rw [hk_eq]
  have hk : my_pi (232806) = 20659 := pi_232806
  have hm0 : my_pi (356590) = 30496 := pi_356590
  have hm1_val : my_pi (357435) = 30555 := pi_357435
  rcases le_or_gt m 844 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 356590 := bound_le_helper m 844 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 845 ≤ m := hm_gt
    have h1 : 357435 ≤ m*(m+1)/2 := bound_gt_helper m 845 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_483 (m : ℕ) (hm1 : m ≥ 1) : my_pi (483*484) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 483*484 = 233772 := by decide
  rw [hk_eq]
  have hk : my_pi (233772) = 20731 := pi_233772
  have hm0 : my_pi (354903) = 30369 := pi_354903
  have hm1_val : my_pi (355746) = 30436 := pi_355746
  rcases le_or_gt m 842 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 354903 := bound_le_helper m 842 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 843 ≤ m := hm_gt
    have h1 : 355746 ≤ m*(m+1)/2 := bound_gt_helper m 843 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_484 (m : ℕ) (hm1 : m ≥ 1) : my_pi (484*485) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 484*485 = 234740 := by decide
  rw [hk_eq]
  have hk : my_pi (234740) = 20808 := pi_234740
  have hm0 : my_pi (354061) = 30299 := pi_354061
  have hm1_val : my_pi (354903) = 30369 := pi_354903
  rcases le_or_gt m 841 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 354061 := bound_le_helper m 841 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 842 ≤ m := hm_gt
    have h1 : 354903 ≤ m*(m+1)/2 := bound_gt_helper m 842 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_485 (m : ℕ) (hm1 : m ≥ 1) : my_pi (485*486) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 485*486 = 235710 := by decide
  rw [hk_eq]
  have hk : my_pi (235710) = 20885 := pi_235710
  have hm0 : my_pi (353220) = 30232 := pi_353220
  have hm1_val : my_pi (354061) = 30299 := pi_354061
  rcases le_or_gt m 840 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 353220 := bound_le_helper m 840 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 841 ≤ m := hm_gt
    have h1 : 354061 ≤ m*(m+1)/2 := bound_gt_helper m 841 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_486 (m : ℕ) (hm1 : m ≥ 1) : my_pi (486*487) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 486*487 = 236682 := by decide
  rw [hk_eq]
  have hk : my_pi (236682) = 20955 := pi_236682
  have hm0 : my_pi (352380) = 30164 := pi_352380
  have hm1_val : my_pi (353220) = 30232 := pi_353220
  rcases le_or_gt m 839 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 352380 := bound_le_helper m 839 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 840 ≤ m := hm_gt
    have h1 : 353220 ≤ m*(m+1)/2 := bound_gt_helper m 840 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_487 (m : ℕ) (hm1 : m ≥ 1) : my_pi (487*488) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 487*488 = 237656 := by decide
  rw [hk_eq]
  have hk : my_pi (237656) = 21027 := pi_237656
  have hm0 : my_pi (351541) = 30098 := pi_351541
  have hm1_val : my_pi (352380) = 30164 := pi_352380
  rcases le_or_gt m 838 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 351541 := bound_le_helper m 838 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 839 ≤ m := hm_gt
    have h1 : 352380 ≤ m*(m+1)/2 := bound_gt_helper m 839 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_488 (m : ℕ) (hm1 : m ≥ 1) : my_pi (488*489) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 488*489 = 238632 := by decide
  rw [hk_eq]
  have hk : my_pi (238632) = 21110 := pi_238632
  have hm0 : my_pi (350703) = 30024 := pi_350703
  have hm1_val : my_pi (351541) = 30098 := pi_351541
  rcases le_or_gt m 837 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 350703 := bound_le_helper m 837 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 838 ≤ m := hm_gt
    have h1 : 351541 ≤ m*(m+1)/2 := bound_gt_helper m 838 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_489 (m : ℕ) (hm1 : m ≥ 1) : my_pi (489*490) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 489*490 = 239610 := by decide
  rw [hk_eq]
  have hk : my_pi (239610) = 21190 := pi_239610
  have hm0 : my_pi (349866) = 29964 := pi_349866
  have hm1_val : my_pi (350703) = 30024 := pi_350703
  rcases le_or_gt m 836 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 349866 := bound_le_helper m 836 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 837 ≤ m := hm_gt
    have h1 : 350703 ≤ m*(m+1)/2 := bound_gt_helper m 837 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_490 (m : ℕ) (hm1 : m ≥ 1) : my_pi (490*491) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 490*491 = 240590 := by decide
  rw [hk_eq]
  have hk : my_pi (240590) = 21268 := pi_240590
  have hm0 : my_pi (348195) = 29831 := pi_348195
  have hm1_val : my_pi (349030) = 29896 := pi_349030
  rcases le_or_gt m 834 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 348195 := bound_le_helper m 834 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 835 ≤ m := hm_gt
    have h1 : 349030 ≤ m*(m+1)/2 := bound_gt_helper m 835 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_491 (m : ℕ) (hm1 : m ≥ 1) : my_pi (491*492) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 491*492 = 241572 := by decide
  rw [hk_eq]
  have hk : my_pi (241572) = 21351 := pi_241572
  have hm0 : my_pi (347361) = 29770 := pi_347361
  have hm1_val : my_pi (348195) = 29831 := pi_348195
  rcases le_or_gt m 833 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 347361 := bound_le_helper m 833 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 834 ≤ m := hm_gt
    have h1 : 348195 ≤ m*(m+1)/2 := bound_gt_helper m 834 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_492 (m : ℕ) (hm1 : m ≥ 1) : my_pi (492*493) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 492*493 = 242556 := by decide
  rw [hk_eq]
  have hk : my_pi (242556) = 21435 := pi_242556
  have hm0 : my_pi (346528) = 29701 := pi_346528
  have hm1_val : my_pi (347361) = 29770 := pi_347361
  rcases le_or_gt m 832 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 346528 := bound_le_helper m 832 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 833 ≤ m := hm_gt
    have h1 : 347361 ≤ m*(m+1)/2 := bound_gt_helper m 833 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_493 (m : ℕ) (hm1 : m ≥ 1) : my_pi (493*494) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 493*494 = 243542 := by decide
  rw [hk_eq]
  have hk : my_pi (243542) = 21511 := pi_243542
  have hm0 : my_pi (345696) = 29630 := pi_345696
  have hm1_val : my_pi (346528) = 29701 := pi_346528
  rcases le_or_gt m 831 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 345696 := bound_le_helper m 831 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 832 ≤ m := hm_gt
    have h1 : 346528 ≤ m*(m+1)/2 := bound_gt_helper m 832 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_494 (m : ℕ) (hm1 : m ≥ 1) : my_pi (494*495) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 494*495 = 244530 := by decide
  rw [hk_eq]
  have hk : my_pi (244530) = 21593 := pi_244530
  have hm0 : my_pi (344035) = 29502 := pi_344035
  have hm1_val : my_pi (344865) = 29568 := pi_344865
  rcases le_or_gt m 829 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 344035 := bound_le_helper m 829 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 830 ≤ m := hm_gt
    have h1 : 344865 ≤ m*(m+1)/2 := bound_gt_helper m 830 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_495 (m : ℕ) (hm1 : m ≥ 1) : my_pi (495*496) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 495*496 = 245520 := by decide
  rw [hk_eq]
  have hk : my_pi (245520) = 21672 := pi_245520
  have hm0 : my_pi (343206) = 29435 := pi_343206
  have hm1_val : my_pi (344035) = 29502 := pi_344035
  rcases le_or_gt m 828 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 343206 := bound_le_helper m 828 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 829 ≤ m := hm_gt
    have h1 : 344035 ≤ m*(m+1)/2 := bound_gt_helper m 829 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_496 (m : ℕ) (hm1 : m ≥ 1) : my_pi (496*497) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 496*497 = 246512 := by decide
  rw [hk_eq]
  have hk : my_pi (246512) = 21752 := pi_246512
  have hm0 : my_pi (342378) = 29376 := pi_342378
  have hm1_val : my_pi (343206) = 29435 := pi_343206
  rcases le_or_gt m 827 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 342378 := bound_le_helper m 827 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 828 ≤ m := hm_gt
    have h1 : 343206 ≤ m*(m+1)/2 := bound_gt_helper m 828 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_497 (m : ℕ) (hm1 : m ≥ 1) : my_pi (497*498) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 497*498 = 247506 := by decide
  rw [hk_eq]
  have hk : my_pi (247506) = 21832 := pi_247506
  have hm0 : my_pi (341551) = 29307 := pi_341551
  have hm1_val : my_pi (342378) = 29376 := pi_342378
  rcases le_or_gt m 826 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 341551 := bound_le_helper m 826 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 827 ≤ m := hm_gt
    have h1 : 342378 ≤ m*(m+1)/2 := bound_gt_helper m 827 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_498 (m : ℕ) (hm1 : m ≥ 1) : my_pi (498*499) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 498*499 = 248502 := by decide
  rw [hk_eq]
  have hk : my_pi (248502) = 21920 := pi_248502
  have hm0 : my_pi (339900) = 29178 := pi_339900
  have hm1_val : my_pi (340725) = 29241 := pi_340725
  rcases le_or_gt m 824 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 339900 := bound_le_helper m 824 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 825 ≤ m := hm_gt
    have h1 : 340725 ≤ m*(m+1)/2 := bound_gt_helper m 825 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_499 (m : ℕ) (hm1 : m ≥ 1) : my_pi (499*500) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 499*500 = 249500 := by decide
  rw [hk_eq]
  have hk : my_pi (249500) = 22004 := pi_249500
  have hm0 : my_pi (339076) = 29118 := pi_339076
  have hm1_val : my_pi (339900) = 29178 := pi_339900
  rcases le_or_gt m 823 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 339076 := bound_le_helper m 823 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 824 ≤ m := hm_gt
    have h1 : 339900 ≤ m*(m+1)/2 := bound_gt_helper m 824 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_500 (m : ℕ) (hm1 : m ≥ 1) : my_pi (500*501) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 500*501 = 250500 := by decide
  rw [hk_eq]
  have hk : my_pi (250500) = 22077 := pi_250500
  have hm0 : my_pi (338253) = 29056 := pi_338253
  have hm1_val : my_pi (339076) = 29118 := pi_339076
  rcases le_or_gt m 822 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 338253 := bound_le_helper m 822 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 823 ≤ m := hm_gt
    have h1 : 339076 ≤ m*(m+1)/2 := bound_gt_helper m 823 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_501 (m : ℕ) (hm1 : m ≥ 1) : my_pi (501*502) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 501*502 = 251502 := by decide
  rw [hk_eq]
  have hk : my_pi (251502) = 22163 := pi_251502
  have hm0 : my_pi (337431) = 28991 := pi_337431
  have hm1_val : my_pi (338253) = 29056 := pi_338253
  rcases le_or_gt m 821 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 337431 := bound_le_helper m 821 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 822 ≤ m := hm_gt
    have h1 : 338253 ≤ m*(m+1)/2 := bound_gt_helper m 822 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_502 (m : ℕ) (hm1 : m ≥ 1) : my_pi (502*503) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 502*503 = 252506 := by decide
  rw [hk_eq]
  have hk : my_pi (252506) = 22243 := pi_252506
  have hm0 : my_pi (335790) = 28858 := pi_335790
  have hm1_val : my_pi (336610) = 28922 := pi_336610
  rcases le_or_gt m 819 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 335790 := bound_le_helper m 819 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 820 ≤ m := hm_gt
    have h1 : 336610 ≤ m*(m+1)/2 := bound_gt_helper m 820 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_503 (m : ℕ) (hm1 : m ≥ 1) : my_pi (503*504) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 503*504 = 253512 := by decide
  rw [hk_eq]
  have hk : my_pi (253512) = 22316 := pi_253512
  have hm0 : my_pi (334971) = 28792 := pi_334971
  have hm1_val : my_pi (335790) = 28858 := pi_335790
  rcases le_or_gt m 818 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 334971 := bound_le_helper m 818 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 819 ≤ m := hm_gt
    have h1 : 335790 ≤ m*(m+1)/2 := bound_gt_helper m 819 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_504 (m : ℕ) (hm1 : m ≥ 1) : my_pi (504*505) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 504*505 = 254520 := by decide
  rw [hk_eq]
  have hk : my_pi (254520) = 22399 := pi_254520
  have hm0 : my_pi (334153) = 28729 := pi_334153
  have hm1_val : my_pi (334971) = 28792 := pi_334971
  rcases le_or_gt m 817 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 334153 := bound_le_helper m 817 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 818 ≤ m := hm_gt
    have h1 : 334971 ≤ m*(m+1)/2 := bound_gt_helper m 818 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_505 (m : ℕ) (hm1 : m ≥ 1) : my_pi (505*506) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 505*506 = 255530 := by decide
  rw [hk_eq]
  have hk : my_pi (255530) = 22486 := pi_255530
  have hm0 : my_pi (333336) = 28665 := pi_333336
  have hm1_val : my_pi (334153) = 28729 := pi_334153
  rcases le_or_gt m 816 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 333336 := bound_le_helper m 816 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 817 ≤ m := hm_gt
    have h1 : 334153 ≤ m*(m+1)/2 := bound_gt_helper m 817 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_506 (m : ℕ) (hm1 : m ≥ 1) : my_pi (506*507) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 506*507 = 256542 := by decide
  rw [hk_eq]
  have hk : my_pi (256542) = 22566 := pi_256542
  have hm0 : my_pi (331705) = 28542 := pi_331705
  have hm1_val : my_pi (332520) = 28607 := pi_332520
  rcases le_or_gt m 814 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 331705 := bound_le_helper m 814 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 815 ≤ m := hm_gt
    have h1 : 332520 ≤ m*(m+1)/2 := bound_gt_helper m 815 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_507 (m : ℕ) (hm1 : m ≥ 1) : my_pi (507*508) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 507*508 = 257556 := by decide
  rw [hk_eq]
  have hk : my_pi (257556) = 22642 := pi_257556
  have hm0 : my_pi (330891) = 28478 := pi_330891
  have hm1_val : my_pi (331705) = 28542 := pi_331705
  rcases le_or_gt m 813 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 330891 := bound_le_helper m 813 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 814 ≤ m := hm_gt
    have h1 : 331705 ≤ m*(m+1)/2 := bound_gt_helper m 814 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_508 (m : ℕ) (hm1 : m ≥ 1) : my_pi (508*509) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 508*509 = 258572 := by decide
  rw [hk_eq]
  have hk : my_pi (258572) = 22724 := pi_258572
  have hm0 : my_pi (330078) = 28412 := pi_330078
  have hm1_val : my_pi (330891) = 28478 := pi_330891
  rcases le_or_gt m 812 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 330078 := bound_le_helper m 812 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 813 ≤ m := hm_gt
    have h1 : 330891 ≤ m*(m+1)/2 := bound_gt_helper m 813 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_509 (m : ℕ) (hm1 : m ≥ 1) : my_pi (509*510) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 509*510 = 259590 := by decide
  rw [hk_eq]
  have hk : my_pi (259590) = 22803 := pi_259590
  have hm0 : my_pi (329266) = 28343 := pi_329266
  have hm1_val : my_pi (330078) = 28412 := pi_330078
  rcases le_or_gt m 811 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 329266 := bound_le_helper m 811 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 812 ≤ m := hm_gt
    have h1 : 330078 ≤ m*(m+1)/2 := bound_gt_helper m 812 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_510 (m : ℕ) (hm1 : m ≥ 1) : my_pi (510*511) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 510*511 = 260610 := by decide
  rw [hk_eq]
  have hk : my_pi (260610) = 22884 := pi_260610
  have hm0 : my_pi (327645) = 28219 := pi_327645
  have hm1_val : my_pi (328455) = 28286 := pi_328455
  rcases le_or_gt m 809 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 327645 := bound_le_helper m 809 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 810 ≤ m := hm_gt
    have h1 : 328455 ≤ m*(m+1)/2 := bound_gt_helper m 810 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_511 (m : ℕ) (hm1 : m ≥ 1) : my_pi (511*512) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 511*512 = 261632 := by decide
  rw [hk_eq]
  have hk : my_pi (261632) = 22962 := pi_261632
  have hm0 : my_pi (326836) = 28150 := pi_326836
  have hm1_val : my_pi (327645) = 28219 := pi_327645
  rcases le_or_gt m 808 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 326836 := bound_le_helper m 808 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 809 ≤ m := hm_gt
    have h1 : 327645 ≤ m*(m+1)/2 := bound_gt_helper m 809 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_512 (m : ℕ) (hm1 : m ≥ 1) : my_pi (512*513) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 512*513 = 262656 := by decide
  rw [hk_eq]
  have hk : my_pi (262656) = 23042 := pi_262656
  have hm0 : my_pi (326028) = 28092 := pi_326028
  have hm1_val : my_pi (326836) = 28150 := pi_326836
  rcases le_or_gt m 807 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 326028 := bound_le_helper m 807 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 808 ≤ m := hm_gt
    have h1 : 326836 ≤ m*(m+1)/2 := bound_gt_helper m 808 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_513 (m : ℕ) (hm1 : m ≥ 1) : my_pi (513*514) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 513*514 = 263682 := by decide
  rw [hk_eq]
  have hk : my_pi (263682) = 23125 := pi_263682
  have hm0 : my_pi (325221) = 28026 := pi_325221
  have hm1_val : my_pi (326028) = 28092 := pi_326028
  rcases le_or_gt m 806 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 325221 := bound_le_helper m 806 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 807 ≤ m := hm_gt
    have h1 : 326028 ≤ m*(m+1)/2 := bound_gt_helper m 807 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_514 (m : ℕ) (hm1 : m ≥ 1) : my_pi (514*515) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 514*515 = 264710 := by decide
  rw [hk_eq]
  have hk : my_pi (264710) = 23202 := pi_264710
  have hm0 : my_pi (324415) = 27951 := pi_324415
  have hm1_val : my_pi (325221) = 28026 := pi_325221
  rcases le_or_gt m 805 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 324415 := bound_le_helper m 805 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 806 ≤ m := hm_gt
    have h1 : 325221 ≤ m*(m+1)/2 := bound_gt_helper m 806 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_515 (m : ℕ) (hm1 : m ≥ 1) : my_pi (515*516) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 515*516 = 265740 := by decide
  rw [hk_eq]
  have hk : my_pi (265740) = 23289 := pi_265740
  have hm0 : my_pi (322806) = 27833 := pi_322806
  have hm1_val : my_pi (323610) = 27894 := pi_323610
  rcases le_or_gt m 803 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 322806 := bound_le_helper m 803 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 804 ≤ m := hm_gt
    have h1 : 323610 ≤ m*(m+1)/2 := bound_gt_helper m 804 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_516 (m : ℕ) (hm1 : m ≥ 1) : my_pi (516*517) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 516*517 = 266772 := by decide
  rw [hk_eq]
  have hk : my_pi (266772) = 23373 := pi_266772
  have hm0 : my_pi (322003) = 27768 := pi_322003
  have hm1_val : my_pi (322806) = 27833 := pi_322806
  rcases le_or_gt m 802 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 322003 := bound_le_helper m 802 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 803 ≤ m := hm_gt
    have h1 : 322806 ≤ m*(m+1)/2 := bound_gt_helper m 803 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_517 (m : ℕ) (hm1 : m ≥ 1) : my_pi (517*518) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 517*518 = 267806 := by decide
  rw [hk_eq]
  have hk : my_pi (267806) = 23473 := pi_267806
  have hm0 : my_pi (320400) = 27644 := pi_320400
  have hm1_val : my_pi (321201) = 27703 := pi_321201
  rcases le_or_gt m 800 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 320400 := bound_le_helper m 800 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 801 ≤ m := hm_gt
    have h1 : 321201 ≤ m*(m+1)/2 := bound_gt_helper m 801 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_518 (m : ℕ) (hm1 : m ≥ 1) : my_pi (518*519) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 518*519 = 268842 := by decide
  rw [hk_eq]
  have hk : my_pi (268842) = 23549 := pi_268842
  have hm0 : my_pi (319600) = 27576 := pi_319600
  have hm1_val : my_pi (320400) = 27644 := pi_320400
  rcases le_or_gt m 799 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 319600 := bound_le_helper m 799 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 800 ≤ m := hm_gt
    have h1 : 320400 ≤ m*(m+1)/2 := bound_gt_helper m 800 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_519 (m : ℕ) (hm1 : m ≥ 1) : my_pi (519*520) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 519*520 = 269880 := by decide
  rw [hk_eq]
  have hk : my_pi (269880) = 23633 := pi_269880
  have hm0 : my_pi (318801) = 27506 := pi_318801
  have hm1_val : my_pi (319600) = 27576 := pi_319600
  rcases le_or_gt m 798 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 318801 := bound_le_helper m 798 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 799 ≤ m := hm_gt
    have h1 : 319600 ≤ m*(m+1)/2 := bound_gt_helper m 799 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_520 (m : ℕ) (hm1 : m ≥ 1) : my_pi (520*521) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 520*521 = 270920 := by decide
  rw [hk_eq]
  have hk : my_pi (270920) = 23719 := pi_270920
  have hm0 : my_pi (317206) = 27373 := pi_317206
  have hm1_val : my_pi (318003) = 27442 := pi_318003
  rcases le_or_gt m 796 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 317206 := bound_le_helper m 796 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 797 ≤ m := hm_gt
    have h1 : 318003 ≤ m*(m+1)/2 := bound_gt_helper m 797 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_521 (m : ℕ) (hm1 : m ≥ 1) : my_pi (521*522) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 521*522 = 271962 := by decide
  rw [hk_eq]
  have hk : my_pi (271962) = 23801 := pi_271962
  have hm0 : my_pi (316410) = 27307 := pi_316410
  have hm1_val : my_pi (317206) = 27373 := pi_317206
  rcases le_or_gt m 795 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 316410 := bound_le_helper m 795 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 796 ≤ m := hm_gt
    have h1 : 317206 ≤ m*(m+1)/2 := bound_gt_helper m 796 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_522 (m : ℕ) (hm1 : m ≥ 1) : my_pi (522*523) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 522*523 = 273006 := by decide
  rw [hk_eq]
  have hk : my_pi (273006) = 23888 := pi_273006
  have hm0 : my_pi (315615) = 27245 := pi_315615
  have hm1_val : my_pi (316410) = 27307 := pi_316410
  rcases le_or_gt m 794 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 315615 := bound_le_helper m 794 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 795 ≤ m := hm_gt
    have h1 : 316410 ≤ m*(m+1)/2 := bound_gt_helper m 795 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_523 (m : ℕ) (hm1 : m ≥ 1) : my_pi (523*524) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 523*524 = 274052 := by decide
  rw [hk_eq]
  have hk : my_pi (274052) = 23961 := pi_274052
  have hm0 : my_pi (314821) = 27185 := pi_314821
  have hm1_val : my_pi (315615) = 27245 := pi_315615
  rcases le_or_gt m 793 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 314821 := bound_le_helper m 793 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 794 ≤ m := hm_gt
    have h1 : 315615 ≤ m*(m+1)/2 := bound_gt_helper m 794 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_524 (m : ℕ) (hm1 : m ≥ 1) : my_pi (524*525) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 524*525 = 275100 := by decide
  rw [hk_eq]
  have hk : my_pi (275100) = 24046 := pi_275100
  have hm0 : my_pi (313236) = 27051 := pi_313236
  have hm1_val : my_pi (314028) = 27122 := pi_314028
  rcases le_or_gt m 791 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 313236 := bound_le_helper m 791 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 792 ≤ m := hm_gt
    have h1 : 314028 ≤ m*(m+1)/2 := bound_gt_helper m 792 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_525 (m : ℕ) (hm1 : m ≥ 1) : my_pi (525*526) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 525*526 = 276150 := by decide
  rw [hk_eq]
  have hk : my_pi (276150) = 24134 := pi_276150
  have hm0 : my_pi (312445) = 26990 := pi_312445
  have hm1_val : my_pi (313236) = 27051 := pi_313236
  rcases le_or_gt m 790 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 312445 := bound_le_helper m 790 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 791 ≤ m := hm_gt
    have h1 : 313236 ≤ m*(m+1)/2 := bound_gt_helper m 791 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_526 (m : ℕ) (hm1 : m ≥ 1) : my_pi (526*527) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 526*527 = 277202 := by decide
  rw [hk_eq]
  have hk : my_pi (277202) = 24218 := pi_277202
  have hm0 : my_pi (311655) = 26924 := pi_311655
  have hm1_val : my_pi (312445) = 26990 := pi_312445
  rcases le_or_gt m 789 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 311655 := bound_le_helper m 789 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 790 ≤ m := hm_gt
    have h1 : 312445 ≤ m*(m+1)/2 := bound_gt_helper m 790 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_527 (m : ℕ) (hm1 : m ≥ 1) : my_pi (527*528) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 527*528 = 278256 := by decide
  rw [hk_eq]
  have hk : my_pi (278256) = 24299 := pi_278256
  have hm0 : my_pi (310078) = 26805 := pi_310078
  have hm1_val : my_pi (310866) = 26869 := pi_310866
  rcases le_or_gt m 787 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 310078 := bound_le_helper m 787 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 788 ≤ m := hm_gt
    have h1 : 310866 ≤ m*(m+1)/2 := bound_gt_helper m 788 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_528 (m : ℕ) (hm1 : m ≥ 1) : my_pi (528*529) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 528*529 = 279312 := by decide
  rw [hk_eq]
  have hk : my_pi (279312) = 24380 := pi_279312
  have hm0 : my_pi (309291) = 26747 := pi_309291
  have hm1_val : my_pi (310078) = 26805 := pi_310078
  rcases le_or_gt m 786 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 309291 := bound_le_helper m 786 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 787 ≤ m := hm_gt
    have h1 : 310078 ≤ m*(m+1)/2 := bound_gt_helper m 787 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_529 (m : ℕ) (hm1 : m ≥ 1) : my_pi (529*530) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 529*530 = 280370 := by decide
  rw [hk_eq]
  have hk : my_pi (280370) = 24463 := pi_280370
  have hm0 : my_pi (308505) = 26682 := pi_308505
  have hm1_val : my_pi (309291) = 26747 := pi_309291
  rcases le_or_gt m 785 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 308505 := bound_le_helper m 785 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 786 ≤ m := hm_gt
    have h1 : 309291 ≤ m*(m+1)/2 := bound_gt_helper m 786 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_530 (m : ℕ) (hm1 : m ≥ 1) : my_pi (530*531) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 530*531 = 281430 := by decide
  rw [hk_eq]
  have hk : my_pi (281430) = 24553 := pi_281430
  have hm0 : my_pi (306936) = 26566 := pi_306936
  have hm1_val : my_pi (307720) = 26630 := pi_307720
  rcases le_or_gt m 783 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 306936 := bound_le_helper m 783 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 784 ≤ m := hm_gt
    have h1 : 307720 ≤ m*(m+1)/2 := bound_gt_helper m 784 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_531 (m : ℕ) (hm1 : m ≥ 1) : my_pi (531*532) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 531*532 = 282492 := by decide
  rw [hk_eq]
  have hk : my_pi (282492) = 24643 := pi_282492
  have hm0 : my_pi (306153) = 26500 := pi_306153
  have hm1_val : my_pi (306936) = 26566 := pi_306936
  rcases le_or_gt m 782 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 306153 := bound_le_helper m 782 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 783 ≤ m := hm_gt
    have h1 : 306936 ≤ m*(m+1)/2 := bound_gt_helper m 783 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_532 (m : ℕ) (hm1 : m ≥ 1) : my_pi (532*533) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 532*533 = 283556 := by decide
  rw [hk_eq]
  have hk : my_pi (283556) = 24719 := pi_283556
  have hm0 : my_pi (304590) = 26373 := pi_304590
  have hm1_val : my_pi (305371) = 26438 := pi_305371
  rcases le_or_gt m 780 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 304590 := bound_le_helper m 780 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 781 ≤ m := hm_gt
    have h1 : 305371 ≤ m*(m+1)/2 := bound_gt_helper m 781 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_533 (m : ℕ) (hm1 : m ≥ 1) : my_pi (533*534) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 533*534 = 284622 := by decide
  rw [hk_eq]
  have hk : my_pi (284622) = 24807 := pi_284622
  have hm0 : my_pi (303810) = 26308 := pi_303810
  have hm1_val : my_pi (304590) = 26373 := pi_304590
  rcases le_or_gt m 779 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 303810 := bound_le_helper m 779 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 780 ≤ m := hm_gt
    have h1 : 304590 ≤ m*(m+1)/2 := bound_gt_helper m 780 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_534 (m : ℕ) (hm1 : m ≥ 1) : my_pi (534*535) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 534*535 = 285690 := by decide
  rw [hk_eq]
  have hk : my_pi (285690) = 24897 := pi_285690
  have hm0 : my_pi (303031) = 26242 := pi_303031
  have hm1_val : my_pi (303810) = 26308 := pi_303810
  rcases le_or_gt m 778 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 303031 := bound_le_helper m 778 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 779 ≤ m := hm_gt
    have h1 : 303810 ≤ m*(m+1)/2 := bound_gt_helper m 779 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_535 (m : ℕ) (hm1 : m ≥ 1) : my_pi (535*536) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 535*536 = 286760 := by decide
  rw [hk_eq]
  have hk : my_pi (286760) = 24977 := pi_286760
  have hm0 : my_pi (302253) = 26178 := pi_302253
  have hm1_val : my_pi (303031) = 26242 := pi_303031
  rcases le_or_gt m 777 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 302253 := bound_le_helper m 777 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 778 ≤ m := hm_gt
    have h1 : 303031 ≤ m*(m+1)/2 := bound_gt_helper m 778 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_536 (m : ℕ) (hm1 : m ≥ 1) : my_pi (536*537) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 536*537 = 287832 := by decide
  rw [hk_eq]
  have hk : my_pi (287832) = 25051 := pi_287832
  have hm0 : my_pi (300700) = 26054 := pi_300700
  have hm1_val : my_pi (301476) = 26120 := pi_301476
  rcases le_or_gt m 775 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 300700 := bound_le_helper m 775 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 776 ≤ m := hm_gt
    have h1 : 301476 ≤ m*(m+1)/2 := bound_gt_helper m 776 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_537 (m : ℕ) (hm1 : m ≥ 1) : my_pi (537*538) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 537*538 = 288906 := by decide
  rw [hk_eq]
  have hk : my_pi (288906) = 25129 := pi_288906
  have hm0 : my_pi (299925) = 25990 := pi_299925
  have hm1_val : my_pi (300700) = 26054 := pi_300700
  rcases le_or_gt m 774 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 299925 := bound_le_helper m 774 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 775 ≤ m := hm_gt
    have h1 : 300700 ≤ m*(m+1)/2 := bound_gt_helper m 775 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_538 (m : ℕ) (hm1 : m ≥ 1) : my_pi (538*539) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 538*539 = 289982 := by decide
  rw [hk_eq]
  have hk : my_pi (289982) = 25222 := pi_289982
  have hm0 : my_pi (299151) = 25932 := pi_299151
  have hm1_val : my_pi (299925) = 25990 := pi_299925
  rcases le_or_gt m 773 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 299151 := bound_le_helper m 773 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 774 ≤ m := hm_gt
    have h1 : 299925 ≤ m*(m+1)/2 := bound_gt_helper m 774 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_539 (m : ℕ) (hm1 : m ≥ 1) : my_pi (539*540) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 539*540 = 291060 := by decide
  rw [hk_eq]
  have hk : my_pi (291060) = 25313 := pi_291060
  have hm0 : my_pi (297606) = 25814 := pi_297606
  have hm1_val : my_pi (298378) = 25877 := pi_298378
  rcases le_or_gt m 771 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 297606 := bound_le_helper m 771 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 772 ≤ m := hm_gt
    have h1 : 298378 ≤ m*(m+1)/2 := bound_gt_helper m 772 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_540 (m : ℕ) (hm1 : m ≥ 1) : my_pi (540*541) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 540*541 = 292140 := by decide
  rw [hk_eq]
  have hk : my_pi (292140) = 25395 := pi_292140
  have hm0 : my_pi (296065) = 25696 := pi_296065
  have hm1_val : my_pi (296835) = 25762 := pi_296835
  rcases le_or_gt m 769 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 296065 := bound_le_helper m 769 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 770 ≤ m := hm_gt
    have h1 : 296835 ≤ m*(m+1)/2 := bound_gt_helper m 770 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_541 (m : ℕ) (hm1 : m ≥ 1) : my_pi (541*542) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 541*542 = 293222 := by decide
  rw [hk_eq]
  have hk : my_pi (293222) = 25481 := pi_293222
  have hm0 : my_pi (295296) = 25639 := pi_295296
  have hm1_val : my_pi (296065) = 25696 := pi_296065
  rcases le_or_gt m 768 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 295296 := bound_le_helper m 768 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 769 ≤ m := hm_gt
    have h1 : 296065 ≤ m*(m+1)/2 := bound_gt_helper m 769 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_542 (m : ℕ) (hm1 : m ≥ 1) : my_pi (542*543) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 542*543 = 294306 := by decide
  rw [hk_eq]
  have hk : my_pi (294306) = 25559 := pi_294306
  have hm0 : my_pi (294528) = 25579 := pi_294528
  have hm1_val : my_pi (295296) = 25639 := pi_295296
  rcases le_or_gt m 767 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 294528 := bound_le_helper m 767 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 768 ≤ m := hm_gt
    have h1 : 295296 ≤ m*(m+1)/2 := bound_gt_helper m 768 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_543 (m : ℕ) (hm1 : m ≥ 1) : my_pi (543*544) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 543*544 = 295392 := by decide
  rw [hk_eq]
  have hk : my_pi (295392) = 25645 := pi_295392
  have hm0 : my_pi (292995) = 25463 := pi_292995
  have hm1_val : my_pi (293761) = 25516 := pi_293761
  rcases le_or_gt m 765 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 292995 := bound_le_helper m 765 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 766 ≤ m := hm_gt
    have h1 : 293761 ≤ m*(m+1)/2 := bound_gt_helper m 766 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_544 (m : ℕ) (hm1 : m ≥ 1) : my_pi (544*545) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 544*545 = 296480 := by decide
  rw [hk_eq]
  have hk : my_pi (296480) = 25726 := pi_296480
  have hm0 : my_pi (292230) = 25401 := pi_292230
  have hm1_val : my_pi (292995) = 25463 := pi_292995
  rcases le_or_gt m 764 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 292230 := bound_le_helper m 764 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 765 ≤ m := hm_gt
    have h1 : 292995 ≤ m*(m+1)/2 := bound_gt_helper m 765 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_545 (m : ℕ) (hm1 : m ≥ 1) : my_pi (545*546) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 545*546 = 297570 := by decide
  rw [hk_eq]
  have hk : my_pi (297570) = 25811 := pi_297570
  have hm0 : my_pi (290703) = 25286 := pi_290703
  have hm1_val : my_pi (291466) = 25346 := pi_291466
  rcases le_or_gt m 762 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 290703 := bound_le_helper m 762 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 763 ≤ m := hm_gt
    have h1 : 291466 ≤ m*(m+1)/2 := bound_gt_helper m 763 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_546 (m : ℕ) (hm1 : m ≥ 1) : my_pi (546*547) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 546*547 = 298662 := by decide
  rw [hk_eq]
  have hk : my_pi (298662) = 25894 := pi_298662
  have hm0 : my_pi (289941) = 25218 := pi_289941
  have hm1_val : my_pi (290703) = 25286 := pi_290703
  rcases le_or_gt m 761 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 289941 := bound_le_helper m 761 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 762 ≤ m := hm_gt
    have h1 : 290703 ≤ m*(m+1)/2 := bound_gt_helper m 762 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_547 (m : ℕ) (hm1 : m ≥ 1) : my_pi (547*548) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 547*548 = 299756 := by decide
  rw [hk_eq]
  have hk : my_pi (299756) = 25980 := pi_299756
  have hm0 : my_pi (289180) = 25159 := pi_289180
  have hm1_val : my_pi (289941) = 25218 := pi_289941
  rcases le_or_gt m 760 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 289180 := bound_le_helper m 760 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 761 ≤ m := hm_gt
    have h1 : 289941 ≤ m*(m+1)/2 := bound_gt_helper m 761 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_548 (m : ℕ) (hm1 : m ≥ 1) : my_pi (548*549) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 548*549 = 300852 := by decide
  rw [hk_eq]
  have hk : my_pi (300852) = 26069 := pi_300852
  have hm0 : my_pi (287661) = 25039 := pi_287661
  have hm1_val : my_pi (288420) = 25093 := pi_288420
  rcases le_or_gt m 758 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 287661 := bound_le_helper m 758 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 759 ≤ m := hm_gt
    have h1 : 288420 ≤ m*(m+1)/2 := bound_gt_helper m 759 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_549 (m : ℕ) (hm1 : m ≥ 1) : my_pi (549*550) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 549*550 = 301950 := by decide
  rw [hk_eq]
  have hk : my_pi (301950) = 26160 := pi_301950
  have hm0 : my_pi (286903) = 24986 := pi_286903
  have hm1_val : my_pi (287661) = 25039 := pi_287661
  rcases le_or_gt m 757 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 286903 := bound_le_helper m 757 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 758 ≤ m := hm_gt
    have h1 : 287661 ≤ m*(m+1)/2 := bound_gt_helper m 758 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_550 (m : ℕ) (hm1 : m ≥ 1) : my_pi (550*551) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 550*551 = 303050 := by decide
  rw [hk_eq]
  have hk : my_pi (303050) = 26243 := pi_303050
  have hm0 : my_pi (285390) = 24871 := pi_285390
  have hm1_val : my_pi (286146) = 24930 := pi_286146
  rcases le_or_gt m 755 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 285390 := bound_le_helper m 755 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 756 ≤ m := hm_gt
    have h1 : 286146 ≤ m*(m+1)/2 := bound_gt_helper m 756 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_551 (m : ℕ) (hm1 : m ≥ 1) : my_pi (551*552) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 551*552 = 304152 := by decide
  rw [hk_eq]
  have hk : my_pi (304152) = 26335 := pi_304152
  have hm0 : my_pi (284635) = 24809 := pi_284635
  have hm1_val : my_pi (285390) = 24871 := pi_285390
  rcases le_or_gt m 754 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 284635 := bound_le_helper m 754 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 755 ≤ m := hm_gt
    have h1 : 285390 ≤ m*(m+1)/2 := bound_gt_helper m 755 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_552 (m : ℕ) (hm1 : m ≥ 1) : my_pi (552*553) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 552*553 = 305256 := by decide
  rw [hk_eq]
  have hk : my_pi (305256) = 26429 := pi_305256
  have hm0 : my_pi (283128) = 24693 := pi_283128
  have hm1_val : my_pi (283881) = 24747 := pi_283881
  rcases le_or_gt m 752 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 283128 := bound_le_helper m 752 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 753 ≤ m := hm_gt
    have h1 : 283881 ≤ m*(m+1)/2 := bound_gt_helper m 753 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_553 (m : ℕ) (hm1 : m ≥ 1) : my_pi (553*554) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 553*554 = 306362 := by decide
  rw [hk_eq]
  have hk : my_pi (306362) = 26517 := pi_306362
  have hm0 : my_pi (282376) = 24631 := pi_282376
  have hm1_val : my_pi (283128) = 24693 := pi_283128
  rcases le_or_gt m 751 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 282376 := bound_le_helper m 751 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 752 ≤ m := hm_gt
    have h1 : 283128 ≤ m*(m+1)/2 := bound_gt_helper m 752 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_554 (m : ℕ) (hm1 : m ≥ 1) : my_pi (554*555) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 554*555 = 307470 := by decide
  rw [hk_eq]
  have hk : my_pi (307470) = 26609 := pi_307470
  have hm0 : my_pi (280875) = 24504 := pi_280875
  have hm1_val : my_pi (281625) = 24567 := pi_281625
  rcases le_or_gt m 749 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 280875 := bound_le_helper m 749 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 750 ≤ m := hm_gt
    have h1 : 281625 ≤ m*(m+1)/2 := bound_gt_helper m 750 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_555 (m : ℕ) (hm1 : m ≥ 1) : my_pi (555*556) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 555*556 = 308580 := by decide
  rw [hk_eq]
  have hk : my_pi (308580) = 26691 := pi_308580
  have hm0 : my_pi (280126) = 24443 := pi_280126
  have hm1_val : my_pi (280875) = 24504 := pi_280875
  rcases le_or_gt m 748 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 280126 := bound_le_helper m 748 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 749 ≤ m := hm_gt
    have h1 : 280875 ≤ m*(m+1)/2 := bound_gt_helper m 749 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_556 (m : ℕ) (hm1 : m ≥ 1) : my_pi (556*557) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 556*557 = 309692 := by decide
  rw [hk_eq]
  have hk : my_pi (309692) = 26780 := pi_309692
  have hm0 : my_pi (278631) = 24330 := pi_278631
  have hm1_val : my_pi (279378) = 24384 := pi_279378
  rcases le_or_gt m 746 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 278631 := bound_le_helper m 746 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 747 ≤ m := hm_gt
    have h1 : 279378 ≤ m*(m+1)/2 := bound_gt_helper m 747 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_557 (m : ℕ) (hm1 : m ≥ 1) : my_pi (557*558) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 557*558 = 310806 := by decide
  rw [hk_eq]
  have hk : my_pi (310806) = 26864 := pi_310806
  have hm0 : my_pi (277885) = 24270 := pi_277885
  have hm1_val : my_pi (278631) = 24330 := pi_278631
  rcases le_or_gt m 745 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 277885 := bound_le_helper m 745 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 746 ≤ m := hm_gt
    have h1 : 278631 ≤ m*(m+1)/2 := bound_gt_helper m 746 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_558 (m : ℕ) (hm1 : m ≥ 1) : my_pi (558*559) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 558*559 = 311922 := by decide
  rw [hk_eq]
  have hk : my_pi (311922) = 26944 := pi_311922
  have hm0 : my_pi (276396) = 24156 := pi_276396
  have hm1_val : my_pi (277140) = 24213 := pi_277140
  rcases le_or_gt m 743 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 276396 := bound_le_helper m 743 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 744 ≤ m := hm_gt
    have h1 : 277140 ≤ m*(m+1)/2 := bound_gt_helper m 744 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_559 (m : ℕ) (hm1 : m ≥ 1) : my_pi (559*560) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 559*560 = 313040 := by decide
  rw [hk_eq]
  have hk : my_pi (313040) = 27038 := pi_313040
  have hm0 : my_pi (275653) = 24093 := pi_275653
  have hm1_val : my_pi (276396) = 24156 := pi_276396
  rcases le_or_gt m 742 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 275653 := bound_le_helper m 742 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 743 ≤ m := hm_gt
    have h1 : 276396 ≤ m*(m+1)/2 := bound_gt_helper m 743 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_560 (m : ℕ) (hm1 : m ≥ 1) : my_pi (560*561) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 560*561 = 314160 := by decide
  rw [hk_eq]
  have hk : my_pi (314160) = 27131 := pi_314160
  have hm0 : my_pi (274170) = 23972 := pi_274170
  have hm1_val : my_pi (274911) = 24031 := pi_274911
  rcases le_or_gt m 740 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 274170 := bound_le_helper m 740 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 741 ≤ m := hm_gt
    have h1 : 274911 ≤ m*(m+1)/2 := bound_gt_helper m 741 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_561 (m : ℕ) (hm1 : m ≥ 1) : my_pi (561*562) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 561*562 = 315282 := by decide
  rw [hk_eq]
  have hk : my_pi (315282) = 27217 := pi_315282
  have hm0 : my_pi (273430) = 23918 := pi_273430
  have hm1_val : my_pi (274170) = 23972 := pi_274170
  rcases le_or_gt m 739 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 273430 := bound_le_helper m 739 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 740 ≤ m := hm_gt
    have h1 : 274170 ≤ m*(m+1)/2 := bound_gt_helper m 740 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_562 (m : ℕ) (hm1 : m ≥ 1) : my_pi (562*563) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 562*563 = 316406 := by decide
  rw [hk_eq]
  have hk : my_pi (316406) = 27307 := pi_316406
  have hm0 : my_pi (271953) = 23801 := pi_271953
  have hm1_val : my_pi (272691) = 23862 := pi_272691
  rcases le_or_gt m 737 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 271953 := bound_le_helper m 737 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 738 ≤ m := hm_gt
    have h1 : 272691 ≤ m*(m+1)/2 := bound_gt_helper m 738 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_563 (m : ℕ) (hm1 : m ≥ 1) : my_pi (563*564) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 563*564 = 317532 := by decide
  rw [hk_eq]
  have hk : my_pi (317532) = 27399 := pi_317532
  have hm0 : my_pi (271216) = 23743 := pi_271216
  have hm1_val : my_pi (271953) = 23801 := pi_271953
  rcases le_or_gt m 736 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 271216 := bound_le_helper m 736 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 737 ≤ m := hm_gt
    have h1 : 271953 ≤ m*(m+1)/2 := bound_gt_helper m 737 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_564 (m : ℕ) (hm1 : m ≥ 1) : my_pi (564*565) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 564*565 = 318660 := by decide
  rw [hk_eq]
  have hk : my_pi (318660) = 27493 := pi_318660
  have hm0 : my_pi (269745) = 23626 := pi_269745
  have hm1_val : my_pi (270480) = 23683 := pi_270480
  rcases le_or_gt m 734 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 269745 := bound_le_helper m 734 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 735 ≤ m := hm_gt
    have h1 : 270480 ≤ m*(m+1)/2 := bound_gt_helper m 735 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_565 (m : ℕ) (hm1 : m ≥ 1) : my_pi (565*566) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 565*566 = 319790 := by decide
  rw [hk_eq]
  have hk : my_pi (319790) = 27591 := pi_319790
  have hm0 : my_pi (269011) = 23564 := pi_269011
  have hm1_val : my_pi (269745) = 23626 := pi_269745
  rcases le_or_gt m 733 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 269011 := bound_le_helper m 733 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 734 ≤ m := hm_gt
    have h1 : 269745 ≤ m*(m+1)/2 := bound_gt_helper m 734 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_566 (m : ℕ) (hm1 : m ≥ 1) : my_pi (566*567) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 566*567 = 320922 := by decide
  rw [hk_eq]
  have hk : my_pi (320922) = 27682 := pi_320922
  have hm0 : my_pi (267546) = 23442 := pi_267546
  have hm1_val : my_pi (268278) = 23508 := pi_268278
  rcases le_or_gt m 731 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 267546 := bound_le_helper m 731 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 732 ≤ m := hm_gt
    have h1 : 268278 ≤ m*(m+1)/2 := bound_gt_helper m 732 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_567 (m : ℕ) (hm1 : m ≥ 1) : my_pi (567*568) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 567*568 = 322056 := by decide
  rw [hk_eq]
  have hk : my_pi (322056) = 27773 := pi_322056
  have hm0 : my_pi (266815) = 23375 := pi_266815
  have hm1_val : my_pi (267546) = 23442 := pi_267546
  rcases le_or_gt m 730 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 266815 := bound_le_helper m 730 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 731 ≤ m := hm_gt
    have h1 : 267546 ≤ m*(m+1)/2 := bound_gt_helper m 731 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_568 (m : ℕ) (hm1 : m ≥ 1) : my_pi (568*569) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 568*569 = 323192 := by decide
  rw [hk_eq]
  have hk : my_pi (323192) = 27861 := pi_323192
  have hm0 : my_pi (265356) = 23259 := pi_265356
  have hm1_val : my_pi (266085) = 23319 := pi_266085
  rcases le_or_gt m 728 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 265356 := bound_le_helper m 728 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 729 ≤ m := hm_gt
    have h1 : 266085 ≤ m*(m+1)/2 := bound_gt_helper m 729 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_569 (m : ℕ) (hm1 : m ≥ 1) : my_pi (569*570) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 569*570 = 324330 := by decide
  rw [hk_eq]
  have hk : my_pi (324330) = 27946 := pi_324330
  have hm0 : my_pi (264628) = 23197 := pi_264628
  have hm1_val : my_pi (265356) = 23259 := pi_265356
  rcases le_or_gt m 727 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 264628 := bound_le_helper m 727 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 728 ≤ m := hm_gt
    have h1 : 265356 ≤ m*(m+1)/2 := bound_gt_helper m 728 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_570 (m : ℕ) (hm1 : m ≥ 1) : my_pi (570*571) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 570*571 = 325470 := by decide
  rw [hk_eq]
  have hk : my_pi (325470) = 28045 := pi_325470
  have hm0 : my_pi (263175) = 23080 := pi_263175
  have hm1_val : my_pi (263901) = 23141 := pi_263901
  rcases le_or_gt m 725 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 263175 := bound_le_helper m 725 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 726 ≤ m := hm_gt
    have h1 : 263901 ≤ m*(m+1)/2 := bound_gt_helper m 726 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_571 (m : ℕ) (hm1 : m ≥ 1) : my_pi (571*572) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 571*572 = 326612 := by decide
  rw [hk_eq]
  have hk : my_pi (326612) = 28135 := pi_326612
  have hm0 : my_pi (261726) = 22970 := pi_261726
  have hm1_val : my_pi (262450) = 23024 := pi_262450
  rcases le_or_gt m 723 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 261726 := bound_le_helper m 723 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 724 ≤ m := hm_gt
    have h1 : 262450 ≤ m*(m+1)/2 := bound_gt_helper m 724 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_572 (m : ℕ) (hm1 : m ≥ 1) : my_pi (572*573) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 572*573 = 327756 := by decide
  rw [hk_eq]
  have hk : my_pi (327756) = 28228 := pi_327756
  have hm0 : my_pi (261003) = 22914 := pi_261003
  have hm1_val : my_pi (261726) = 22970 := pi_261726
  rcases le_or_gt m 722 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 261003 := bound_le_helper m 722 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 723 ≤ m := hm_gt
    have h1 : 261726 ≤ m*(m+1)/2 := bound_gt_helper m 723 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_573 (m : ℕ) (hm1 : m ≥ 1) : my_pi (573*574) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 573*574 = 328902 := by decide
  rw [hk_eq]
  have hk : my_pi (328902) = 28318 := pi_328902
  have hm0 : my_pi (259560) = 22801 := pi_259560
  have hm1_val : my_pi (260281) = 22858 := pi_260281
  rcases le_or_gt m 720 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 259560 := bound_le_helper m 720 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 721 ≤ m := hm_gt
    have h1 : 260281 ≤ m*(m+1)/2 := bound_gt_helper m 721 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_574 (m : ℕ) (hm1 : m ≥ 1) : my_pi (574*575) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 574*575 = 330050 := by decide
  rw [hk_eq]
  have hk : my_pi (330050) = 28409 := pi_330050
  have hm0 : my_pi (258121) = 22685 := pi_258121
  have hm1_val : my_pi (258840) = 22749 := pi_258840
  rcases le_or_gt m 718 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 258121 := bound_le_helper m 718 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 719 ≤ m := hm_gt
    have h1 : 258840 ≤ m*(m+1)/2 := bound_gt_helper m 719 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_575 (m : ℕ) (hm1 : m ≥ 1) : my_pi (575*576) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 575*576 = 331200 := by decide
  rw [hk_eq]
  have hk : my_pi (331200) = 28498 := pi_331200
  have hm0 : my_pi (257403) = 22630 := pi_257403
  have hm1_val : my_pi (258121) = 22685 := pi_258121
  rcases le_or_gt m 717 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 257403 := bound_le_helper m 717 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 718 ≤ m := hm_gt
    have h1 : 258121 ≤ m*(m+1)/2 := bound_gt_helper m 718 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_576 (m : ℕ) (hm1 : m ≥ 1) : my_pi (576*577) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 576*577 = 332352 := by decide
  rw [hk_eq]
  have hk : my_pi (332352) = 28593 := pi_332352
  have hm0 : my_pi (255970) = 22521 := pi_255970
  have hm1_val : my_pi (256686) = 22577 := pi_256686
  rcases le_or_gt m 715 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 255970 := bound_le_helper m 715 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 716 ≤ m := hm_gt
    have h1 : 256686 ≤ m*(m+1)/2 := bound_gt_helper m 716 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_577 (m : ℕ) (hm1 : m ≥ 1) : my_pi (577*578) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 577*578 = 333506 := by decide
  rw [hk_eq]
  have hk : my_pi (333506) = 28683 := pi_333506
  have hm0 : my_pi (255255) = 22466 := pi_255255
  have hm1_val : my_pi (255970) = 22521 := pi_255970
  rcases le_or_gt m 714 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 255255 := bound_le_helper m 714 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 715 ≤ m := hm_gt
    have h1 : 255970 ≤ m*(m+1)/2 := bound_gt_helper m 715 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_578 (m : ℕ) (hm1 : m ≥ 1) : my_pi (578*579) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 578*579 = 334662 := by decide
  rw [hk_eq]
  have hk : my_pi (334662) = 28769 := pi_334662
  have hm0 : my_pi (253828) = 22347 := pi_253828
  have hm1_val : my_pi (254541) = 22400 := pi_254541
  rcases le_or_gt m 712 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 253828 := bound_le_helper m 712 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 713 ≤ m := hm_gt
    have h1 : 254541 ≤ m*(m+1)/2 := bound_gt_helper m 713 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_579 (m : ℕ) (hm1 : m ≥ 1) : my_pi (579*580) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 579*580 = 335820 := by decide
  rw [hk_eq]
  have hk : my_pi (335820) = 28861 := pi_335820
  have hm0 : my_pi (253116) = 22288 := pi_253116
  have hm1_val : my_pi (253828) = 22347 := pi_253828
  rcases le_or_gt m 711 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 253116 := bound_le_helper m 711 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 712 ≤ m := hm_gt
    have h1 : 253828 ≤ m*(m+1)/2 := bound_gt_helper m 712 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_580 (m : ℕ) (hm1 : m ≥ 1) : my_pi (580*581) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 580*581 = 336980 := by decide
  rw [hk_eq]
  have hk : my_pi (336980) = 28954 := pi_336980
  have hm0 : my_pi (251695) = 22179 := pi_251695
  have hm1_val : my_pi (252405) = 22235 := pi_252405
  rcases le_or_gt m 709 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 251695 := bound_le_helper m 709 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 710 ≤ m := hm_gt
    have h1 : 252405 ≤ m*(m+1)/2 := bound_gt_helper m 710 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_581 (m : ℕ) (hm1 : m ≥ 1) : my_pi (581*582) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 581*582 = 338142 := by decide
  rw [hk_eq]
  have hk : my_pi (338142) = 29043 := pi_338142
  have hm0 : my_pi (250278) = 22064 := pi_250278
  have hm1_val : my_pi (250986) = 22114 := pi_250986
  rcases le_or_gt m 707 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 250278 := bound_le_helper m 707 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 708 ≤ m := hm_gt
    have h1 : 250986 ≤ m*(m+1)/2 := bound_gt_helper m 708 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_582 (m : ℕ) (hm1 : m ≥ 1) : my_pi (582*583) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 582*583 = 339306 := by decide
  rw [hk_eq]
  have hk : my_pi (339306) = 29136 := pi_339306
  have hm0 : my_pi (249571) = 22011 := pi_249571
  have hm1_val : my_pi (250278) = 22064 := pi_250278
  rcases le_or_gt m 706 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 249571 := bound_le_helper m 706 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 707 ≤ m := hm_gt
    have h1 : 250278 ≤ m*(m+1)/2 := bound_gt_helper m 707 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_583 (m : ℕ) (hm1 : m ≥ 1) : my_pi (583*584) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 583*584 = 340472 := by decide
  rw [hk_eq]
  have hk : my_pi (340472) = 29220 := pi_340472
  have hm0 : my_pi (248160) = 21890 := pi_248160
  have hm1_val : my_pi (248865) = 21953 := pi_248865
  rcases le_or_gt m 704 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 248160 := bound_le_helper m 704 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 705 ≤ m := hm_gt
    have h1 : 248865 ≤ m*(m+1)/2 := bound_gt_helper m 705 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_584 (m : ℕ) (hm1 : m ≥ 1) : my_pi (584*585) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 584*585 = 341640 := by decide
  rw [hk_eq]
  have hk : my_pi (341640) = 29315 := pi_341640
  have hm0 : my_pi (247456) = 21830 := pi_247456
  have hm1_val : my_pi (248160) = 21890 := pi_248160
  rcases le_or_gt m 703 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 247456 := bound_le_helper m 703 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 704 ≤ m := hm_gt
    have h1 : 248160 ≤ m*(m+1)/2 := bound_gt_helper m 704 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_585 (m : ℕ) (hm1 : m ≥ 1) : my_pi (585*586) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 585*586 = 342810 := by decide
  rw [hk_eq]
  have hk : my_pi (342810) = 29407 := pi_342810
  have hm0 : my_pi (246051) = 21716 := pi_246051
  have hm1_val : my_pi (246753) = 21773 := pi_246753
  rcases le_or_gt m 701 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 246051 := bound_le_helper m 701 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 702 ≤ m := hm_gt
    have h1 : 246753 ≤ m*(m+1)/2 := bound_gt_helper m 702 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_586 (m : ℕ) (hm1 : m ≥ 1) : my_pi (586*587) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 586*587 = 343982 := by decide
  rw [hk_eq]
  have hk : my_pi (343982) = 29499 := pi_343982
  have hm0 : my_pi (244650) = 21605 := pi_244650
  have hm1_val : my_pi (245350) = 21659 := pi_245350
  rcases le_or_gt m 699 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 244650 := bound_le_helper m 699 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 700 ≤ m := hm_gt
    have h1 : 245350 ≤ m*(m+1)/2 := bound_gt_helper m 700 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_587 (m : ℕ) (hm1 : m ≥ 1) : my_pi (587*588) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 587*588 = 345156 := by decide
  rw [hk_eq]
  have hk : my_pi (345156) = 29592 := pi_345156
  have hm0 : my_pi (243951) = 21542 := pi_243951
  have hm1_val : my_pi (244650) = 21605 := pi_244650
  rcases le_or_gt m 698 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 243951 := bound_le_helper m 698 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 699 ≤ m := hm_gt
    have h1 : 244650 ≤ m*(m+1)/2 := bound_gt_helper m 699 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_588 (m : ℕ) (hm1 : m ≥ 1) : my_pi (588*589) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 588*589 = 346332 := by decide
  rw [hk_eq]
  have hk : my_pi (346332) = 29682 := pi_346332
  have hm0 : my_pi (242556) = 21435 := pi_242556
  have hm1_val : my_pi (243253) = 21488 := pi_243253
  rcases le_or_gt m 696 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 242556 := bound_le_helper m 696 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 697 ≤ m := hm_gt
    have h1 : 243253 ≤ m*(m+1)/2 := bound_gt_helper m 697 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_589 (m : ℕ) (hm1 : m ≥ 1) : my_pi (589*590) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 589*590 = 347510 := by decide
  rw [hk_eq]
  have hk : my_pi (347510) = 29776 := pi_347510
  have hm0 : my_pi (241860) = 21375 := pi_241860
  have hm1_val : my_pi (242556) = 21435 := pi_242556
  rcases le_or_gt m 695 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 241860 := bound_le_helper m 695 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 696 ≤ m := hm_gt
    have h1 : 242556 ≤ m*(m+1)/2 := bound_gt_helper m 696 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_590 (m : ℕ) (hm1 : m ≥ 1) : my_pi (590*591) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 590*591 = 348690 := by decide
  rw [hk_eq]
  have hk : my_pi (348690) = 29873 := pi_348690
  have hm0 : my_pi (240471) = 21258 := pi_240471
  have hm1_val : my_pi (241165) = 21314 := pi_241165
  rcases le_or_gt m 693 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 240471 := bound_le_helper m 693 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 694 ≤ m := hm_gt
    have h1 : 241165 ≤ m*(m+1)/2 := bound_gt_helper m 694 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_591 (m : ℕ) (hm1 : m ≥ 1) : my_pi (591*592) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 591*592 = 349872 := by decide
  rw [hk_eq]
  have hk : my_pi (349872) = 29965 := pi_349872
  have hm0 : my_pi (239086) = 21148 := pi_239086
  have hm1_val : my_pi (239778) = 21202 := pi_239778
  rcases le_or_gt m 691 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 239086 := bound_le_helper m 691 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 692 ≤ m := hm_gt
    have h1 : 239778 ≤ m*(m+1)/2 := bound_gt_helper m 692 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_592 (m : ℕ) (hm1 : m ≥ 1) : my_pi (592*593) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 592*593 = 351056 := by decide
  rw [hk_eq]
  have hk : my_pi (351056) = 30058 := pi_351056
  have hm0 : my_pi (238395) = 21093 := pi_238395
  have hm1_val : my_pi (239086) = 21148 := pi_239086
  rcases le_or_gt m 690 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 238395 := bound_le_helper m 690 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 691 ≤ m := hm_gt
    have h1 : 239086 ≤ m*(m+1)/2 := bound_gt_helper m 691 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_593 (m : ℕ) (hm1 : m ≥ 1) : my_pi (593*594) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 593*594 = 352242 := by decide
  rw [hk_eq]
  have hk : my_pi (352242) = 30151 := pi_352242
  have hm0 : my_pi (237016) = 20983 := pi_237016
  have hm1_val : my_pi (237705) = 21032 := pi_237705
  rcases le_or_gt m 688 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 237016 := bound_le_helper m 688 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 689 ≤ m := hm_gt
    have h1 : 237705 ≤ m*(m+1)/2 := bound_gt_helper m 689 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_594 (m : ℕ) (hm1 : m ≥ 1) : my_pi (594*595) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 594*595 = 353430 := by decide
  rw [hk_eq]
  have hk : my_pi (353430) = 30245 := pi_353430
  have hm0 : my_pi (235641) = 20880 := pi_235641
  have hm1_val : my_pi (236328) = 20928 := pi_236328
  rcases le_or_gt m 686 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 235641 := bound_le_helper m 686 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 687 ≤ m := hm_gt
    have h1 : 236328 ≤ m*(m+1)/2 := bound_gt_helper m 687 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_595 (m : ℕ) (hm1 : m ≥ 1) : my_pi (595*596) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 595*596 = 354620 := by decide
  rw [hk_eq]
  have hk : my_pi (354620) = 30345 := pi_354620
  have hm0 : my_pi (234270) = 20769 := pi_234270
  have hm1_val : my_pi (234955) = 20827 := pi_234955
  rcases le_or_gt m 684 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 234270 := bound_le_helper m 684 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 685 ≤ m := hm_gt
    have h1 : 234955 ≤ m*(m+1)/2 := bound_gt_helper m 685 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_596 (m : ℕ) (hm1 : m ≥ 1) : my_pi (596*597) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 596*597 = 355812 := by decide
  rw [hk_eq]
  have hk : my_pi (355812) = 30442 := pi_355812
  have hm0 : my_pi (232903) = 20669 := pi_232903
  have hm1_val : my_pi (233586) = 20715 := pi_233586
  rcases le_or_gt m 682 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 232903 := bound_le_helper m 682 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 683 ≤ m := hm_gt
    have h1 : 233586 ≤ m*(m+1)/2 := bound_gt_helper m 683 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_597 (m : ℕ) (hm1 : m ≥ 1) : my_pi (597*598) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 597*598 = 357006 := by decide
  rw [hk_eq]
  have hk : my_pi (357006) = 30523 := pi_357006
  have hm0 : my_pi (232221) = 20618 := pi_232221
  have hm1_val : my_pi (232903) = 20669 := pi_232903
  rcases le_or_gt m 681 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 232221 := bound_le_helper m 681 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 682 ≤ m := hm_gt
    have h1 : 232903 ≤ m*(m+1)/2 := bound_gt_helper m 682 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_598 (m : ℕ) (hm1 : m ≥ 1) : my_pi (598*599) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 598*599 = 358202 := by decide
  rw [hk_eq]
  have hk : my_pi (358202) = 30615 := pi_358202
  have hm0 : my_pi (230860) = 20509 := pi_230860
  have hm1_val : my_pi (231540) = 20563 := pi_231540
  rcases le_or_gt m 679 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 230860 := bound_le_helper m 679 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 680 ≤ m := hm_gt
    have h1 : 231540 ≤ m*(m+1)/2 := bound_gt_helper m 680 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_599 (m : ℕ) (hm1 : m ≥ 1) : my_pi (599*600) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 599*600 = 359400 := by decide
  rw [hk_eq]
  have hk : my_pi (359400) = 30718 := pi_359400
  have hm0 : my_pi (229503) = 20389 := pi_229503
  have hm1_val : my_pi (230181) = 20452 := pi_230181
  rcases le_or_gt m 677 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 229503 := bound_le_helper m 677 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 678 ≤ m := hm_gt
    have h1 : 230181 ≤ m*(m+1)/2 := bound_gt_helper m 678 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_600 (m : ℕ) (hm1 : m ≥ 1) : my_pi (600*601) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 600*601 = 360600 := by decide
  rw [hk_eq]
  have hk : my_pi (360600) = 30798 := pi_360600
  have hm0 : my_pi (228826) = 20330 := pi_228826
  have hm1_val : my_pi (229503) = 20389 := pi_229503
  rcases le_or_gt m 676 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 228826 := bound_le_helper m 676 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 677 ≤ m := hm_gt
    have h1 : 229503 ≤ m*(m+1)/2 := bound_gt_helper m 677 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_601 (m : ℕ) (hm1 : m ≥ 1) : my_pi (601*602) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 601*602 = 361802 := by decide
  rw [hk_eq]
  have hk : my_pi (361802) = 30888 := pi_361802
  have hm0 : my_pi (227475) = 20220 := pi_227475
  have hm1_val : my_pi (228150) = 20271 := pi_228150
  rcases le_or_gt m 674 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 227475 := bound_le_helper m 674 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 675 ≤ m := hm_gt
    have h1 : 228150 ≤ m*(m+1)/2 := bound_gt_helper m 675 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_602 (m : ℕ) (hm1 : m ≥ 1) : my_pi (602*603) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 602*603 = 363006 := by decide
  rw [hk_eq]
  have hk : my_pi (363006) = 30980 := pi_363006
  have hm0 : my_pi (226801) = 20167 := pi_226801
  have hm1_val : my_pi (227475) = 20220 := pi_227475
  rcases le_or_gt m 673 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 226801 := bound_le_helper m 673 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 674 ≤ m := hm_gt
    have h1 : 227475 ≤ m*(m+1)/2 := bound_gt_helper m 674 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_603 (m : ℕ) (hm1 : m ≥ 1) : my_pi (603*604) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 603*604 = 364212 := by decide
  rw [hk_eq]
  have hk : my_pi (364212) = 31077 := pi_364212
  have hm0 : my_pi (225456) = 20057 := pi_225456
  have hm1_val : my_pi (226128) = 20113 := pi_226128
  rcases le_or_gt m 671 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 225456 := bound_le_helper m 671 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 672 ≤ m := hm_gt
    have h1 : 226128 ≤ m*(m+1)/2 := bound_gt_helper m 672 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_604 (m : ℕ) (hm1 : m ≥ 1) : my_pi (604*605) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 604*605 = 365420 := by decide
  rw [hk_eq]
  have hk : my_pi (365420) = 31174 := pi_365420
  have hm0 : my_pi (224115) = 19947 := pi_224115
  have hm1_val : my_pi (224785) = 20003 := pi_224785
  rcases le_or_gt m 669 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 224115 := bound_le_helper m 669 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 670 ≤ m := hm_gt
    have h1 : 224785 ≤ m*(m+1)/2 := bound_gt_helper m 670 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_605 (m : ℕ) (hm1 : m ≥ 1) : my_pi (605*606) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 605*606 = 366630 := by decide
  rw [hk_eq]
  have hk : my_pi (366630) = 31272 := pi_366630
  have hm0 : my_pi (222778) = 19835 := pi_222778
  have hm1_val : my_pi (223446) = 19899 := pi_223446
  rcases le_or_gt m 667 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 222778 := bound_le_helper m 667 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 668 ≤ m := hm_gt
    have h1 : 223446 ≤ m*(m+1)/2 := bound_gt_helper m 668 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_606 (m : ℕ) (hm1 : m ≥ 1) : my_pi (606*607) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 606*607 = 367842 := by decide
  rw [hk_eq]
  have hk : my_pi (367842) = 31373 := pi_367842
  have hm0 : my_pi (221445) = 19729 := pi_221445
  have hm1_val : my_pi (222111) = 19787 := pi_222111
  rcases le_or_gt m 665 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 221445 := bound_le_helper m 665 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 666 ≤ m := hm_gt
    have h1 : 222111 ≤ m*(m+1)/2 := bound_gt_helper m 666 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_607 (m : ℕ) (hm1 : m ≥ 1) : my_pi (607*608) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 607*608 = 369056 := by decide
  rw [hk_eq]
  have hk : my_pi (369056) = 31458 := pi_369056
  have hm0 : my_pi (220780) = 19675 := pi_220780
  have hm1_val : my_pi (221445) = 19729 := pi_221445
  rcases le_or_gt m 664 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 220780 := bound_le_helper m 664 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 665 ≤ m := hm_gt
    have h1 : 221445 ≤ m*(m+1)/2 := bound_gt_helper m 665 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_608 (m : ℕ) (hm1 : m ≥ 1) : my_pi (608*609) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 608*609 = 370272 := by decide
  rw [hk_eq]
  have hk : my_pi (370272) = 31545 := pi_370272
  have hm0 : my_pi (219453) = 19563 := pi_219453
  have hm1_val : my_pi (220116) = 19624 := pi_220116
  rcases le_or_gt m 662 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 219453 := bound_le_helper m 662 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 663 ≤ m := hm_gt
    have h1 : 220116 ≤ m*(m+1)/2 := bound_gt_helper m 663 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_609 (m : ℕ) (hm1 : m ≥ 1) : my_pi (609*610) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 609*610 = 371490 := by decide
  rw [hk_eq]
  have hk : my_pi (371490) = 31633 := pi_371490
  have hm0 : my_pi (218791) = 19508 := pi_218791
  have hm1_val : my_pi (219453) = 19563 := pi_219453
  rcases le_or_gt m 661 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 218791 := bound_le_helper m 661 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 662 ≤ m := hm_gt
    have h1 : 219453 ≤ m*(m+1)/2 := bound_gt_helper m 662 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_610 (m : ℕ) (hm1 : m ≥ 1) : my_pi (610*611) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 610*611 = 372710 := by decide
  rw [hk_eq]
  have hk : my_pi (372710) = 31723 := pi_372710
  have hm0 : my_pi (217470) = 19406 := pi_217470
  have hm1_val : my_pi (218130) = 19454 := pi_218130
  rcases le_or_gt m 659 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 217470 := bound_le_helper m 659 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 660 ≤ m := hm_gt
    have h1 : 218130 ≤ m*(m+1)/2 := bound_gt_helper m 660 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_611 (m : ℕ) (hm1 : m ≥ 1) : my_pi (611*612) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 611*612 = 373932 := by decide
  rw [hk_eq]
  have hk : my_pi (373932) = 31814 := pi_373932
  have hm0 : my_pi (216153) = 19299 := pi_216153
  have hm1_val : my_pi (216811) = 19349 := pi_216811
  rcases le_or_gt m 657 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 216153 := bound_le_helper m 657 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 658 ≤ m := hm_gt
    have h1 : 216811 ≤ m*(m+1)/2 := bound_gt_helper m 658 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_612 (m : ℕ) (hm1 : m ≥ 1) : my_pi (612*613) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 612*613 = 375156 := by decide
  rw [hk_eq]
  have hk : my_pi (375156) = 31920 := pi_375156
  have hm0 : my_pi (214840) = 19202 := pi_214840
  have hm1_val : my_pi (215496) = 19249 := pi_215496
  rcases le_or_gt m 655 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 214840 := bound_le_helper m 655 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 656 ≤ m := hm_gt
    have h1 : 215496 ≤ m*(m+1)/2 := bound_gt_helper m 656 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_613 (m : ℕ) (hm1 : m ≥ 1) : my_pi (613*614) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 613*614 = 376382 := by decide
  rw [hk_eq]
  have hk : my_pi (376382) = 32015 := pi_376382
  have hm0 : my_pi (213531) = 19090 := pi_213531
  have hm1_val : my_pi (214185) = 19145 := pi_214185
  rcases le_or_gt m 653 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 213531 := bound_le_helper m 653 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 654 ≤ m := hm_gt
    have h1 : 214185 ≤ m*(m+1)/2 := bound_gt_helper m 654 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_614 (m : ℕ) (hm1 : m ≥ 1) : my_pi (614*615) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 614*615 = 377610 := by decide
  rw [hk_eq]
  have hk : my_pi (377610) = 32114 := pi_377610
  have hm0 : my_pi (212878) = 19036 := pi_212878
  have hm1_val : my_pi (213531) = 19090 := pi_213531
  rcases le_or_gt m 652 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 212878 := bound_le_helper m 652 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 653 ≤ m := hm_gt
    have h1 : 213531 ≤ m*(m+1)/2 := bound_gt_helper m 653 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_615 (m : ℕ) (hm1 : m ≥ 1) : my_pi (615*616) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 615*616 = 378840 := by decide
  rw [hk_eq]
  have hk : my_pi (378840) = 32205 := pi_378840
  have hm0 : my_pi (211575) = 18940 := pi_211575
  have hm1_val : my_pi (212226) = 18992 := pi_212226
  rcases le_or_gt m 650 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 211575 := bound_le_helper m 650 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 651 ≤ m := hm_gt
    have h1 : 212226 ≤ m*(m+1)/2 := bound_gt_helper m 651 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_616 (m : ℕ) (hm1 : m ≥ 1) : my_pi (616*617) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 616*617 = 380072 := by decide
  rw [hk_eq]
  have hk : my_pi (380072) = 32304 := pi_380072
  have hm0 : my_pi (210276) = 18834 := pi_210276
  have hm1_val : my_pi (210925) = 18887 := pi_210925
  rcases le_or_gt m 648 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 210276 := bound_le_helper m 648 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 649 ≤ m := hm_gt
    have h1 : 210925 ≤ m*(m+1)/2 := bound_gt_helper m 649 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_617 (m : ℕ) (hm1 : m ≥ 1) : my_pi (617*618) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 617*618 = 381306 := by decide
  rw [hk_eq]
  have hk : my_pi (381306) = 32394 := pi_381306
  have hm0 : my_pi (208981) = 18716 := pi_208981
  have hm1_val : my_pi (209628) = 18774 := pi_209628
  rcases le_or_gt m 646 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 208981 := bound_le_helper m 646 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 647 ≤ m := hm_gt
    have h1 : 209628 ≤ m*(m+1)/2 := bound_gt_helper m 647 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_618 (m : ℕ) (hm1 : m ≥ 1) : my_pi (618*619) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 618*619 = 382542 := by decide
  rw [hk_eq]
  have hk : my_pi (382542) = 32483 := pi_382542
  have hm0 : my_pi (208335) = 18664 := pi_208335
  have hm1_val : my_pi (208981) = 18716 := pi_208981
  rcases le_or_gt m 645 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 208335 := bound_le_helper m 645 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 646 ≤ m := hm_gt
    have h1 : 208981 ≤ m*(m+1)/2 := bound_gt_helper m 646 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_619 (m : ℕ) (hm1 : m ≥ 1) : my_pi (619*620) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 619*620 = 383780 := by decide
  rw [hk_eq]
  have hk : my_pi (383780) = 32584 := pi_383780
  have hm0 : my_pi (207046) = 18552 := pi_207046
  have hm1_val : my_pi (207690) = 18611 := pi_207690
  rcases le_or_gt m 643 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 207046 := bound_le_helper m 643 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 644 ≤ m := hm_gt
    have h1 : 207690 ≤ m*(m+1)/2 := bound_gt_helper m 644 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_620 (m : ℕ) (hm1 : m ≥ 1) : my_pi (620*621) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 620*621 = 385020 := by decide
  rw [hk_eq]
  have hk : my_pi (385020) = 32683 := pi_385020
  have hm0 : my_pi (205761) = 18446 := pi_205761
  have hm1_val : my_pi (206403) = 18502 := pi_206403
  rcases le_or_gt m 641 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 205761 := bound_le_helper m 641 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 642 ≤ m := hm_gt
    have h1 : 206403 ≤ m*(m+1)/2 := bound_gt_helper m 642 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_621 (m : ℕ) (hm1 : m ≥ 1) : my_pi (621*622) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 621*622 = 386262 := by decide
  rw [hk_eq]
  have hk : my_pi (386262) = 32783 := pi_386262
  have hm0 : my_pi (204480) = 18341 := pi_204480
  have hm1_val : my_pi (205120) = 18391 := pi_205120
  rcases le_or_gt m 639 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 204480 := bound_le_helper m 639 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 640 ≤ m := hm_gt
    have h1 : 205120 ≤ m*(m+1)/2 := bound_gt_helper m 640 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_622 (m : ℕ) (hm1 : m ≥ 1) : my_pi (622*623) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 622*623 = 387506 := by decide
  rw [hk_eq]
  have hk : my_pi (387506) = 32875 := pi_387506
  have hm0 : my_pi (203203) = 18236 := pi_203203
  have hm1_val : my_pi (203841) = 18289 := pi_203841
  rcases le_or_gt m 637 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 203203 := bound_le_helper m 637 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 638 ≤ m := hm_gt
    have h1 : 203841 ≤ m*(m+1)/2 := bound_gt_helper m 638 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_623 (m : ℕ) (hm1 : m ≥ 1) : my_pi (623*624) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 623*624 = 388752 := by decide
  rw [hk_eq]
  have hk : my_pi (388752) = 32963 := pi_388752
  have hm0 : my_pi (202566) = 18188 := pi_202566
  have hm1_val : my_pi (203203) = 18236 := pi_203203
  rcases le_or_gt m 636 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 202566 := bound_le_helper m 636 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 637 ≤ m := hm_gt
    have h1 : 203203 ≤ m*(m+1)/2 := bound_gt_helper m 637 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_624 (m : ℕ) (hm1 : m ≥ 1) : my_pi (624*625) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 624*625 = 390000 := by decide
  rw [hk_eq]
  have hk : my_pi (390000) = 33067 := pi_390000
  have hm0 : my_pi (201295) = 18084 := pi_201295
  have hm1_val : my_pi (201930) = 18141 := pi_201930
  rcases le_or_gt m 634 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 201295 := bound_le_helper m 634 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 635 ≤ m := hm_gt
    have h1 : 201930 ≤ m*(m+1)/2 := bound_gt_helper m 635 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_625 (m : ℕ) (hm1 : m ≥ 1) : my_pi (625*626) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 625*626 = 391250 := by decide
  rw [hk_eq]
  have hk : my_pi (391250) = 33170 := pi_391250
  have hm0 : my_pi (199396) = 17932 := pi_199396
  have hm1_val : my_pi (200028) = 17988 := pi_200028
  rcases le_or_gt m 631 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 199396 := bound_le_helper m 631 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 632 ≤ m := hm_gt
    have h1 : 200028 ≤ m*(m+1)/2 := bound_gt_helper m 632 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_626 (m : ℕ) (hm1 : m ≥ 1) : my_pi (626*627) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 626*627 = 392502 := by decide
  rw [hk_eq]
  have hk : my_pi (392502) = 33273 := pi_392502
  have hm0 : my_pi (198135) = 17832 := pi_198135
  have hm1_val : my_pi (198765) = 17884 := pi_198765
  rcases le_or_gt m 629 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 198135 := bound_le_helper m 629 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 630 ≤ m := hm_gt
    have h1 : 198765 ≤ m*(m+1)/2 := bound_gt_helper m 630 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_627 (m : ℕ) (hm1 : m ≥ 1) : my_pi (627*628) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 627*628 = 393756 := by decide
  rw [hk_eq]
  have hk : my_pi (393756) = 33382 := pi_393756
  have hm0 : my_pi (196878) = 17726 := pi_196878
  have hm1_val : my_pi (197506) = 17778 := pi_197506
  rcases le_or_gt m 627 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 196878 := bound_le_helper m 627 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 628 ≤ m := hm_gt
    have h1 : 197506 ≤ m*(m+1)/2 := bound_gt_helper m 628 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_628 (m : ℕ) (hm1 : m ≥ 1) : my_pi (628*629) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 628*629 = 395012 := by decide
  rw [hk_eq]
  have hk : my_pi (395012) = 33475 := pi_395012
  have hm0 : my_pi (196251) = 17678 := pi_196251
  have hm1_val : my_pi (196878) = 17726 := pi_196878
  rcases le_or_gt m 626 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 196251 := bound_le_helper m 626 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 627 ≤ m := hm_gt
    have h1 : 196878 ≤ m*(m+1)/2 := bound_gt_helper m 627 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_629 (m : ℕ) (hm1 : m ≥ 1) : my_pi (629*630) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 629*630 = 396270 := by decide
  rw [hk_eq]
  have hk : my_pi (396270) = 33569 := pi_396270
  have hm0 : my_pi (195000) = 17573 := pi_195000
  have hm1_val : my_pi (195625) = 17625 := pi_195625
  rcases le_or_gt m 624 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 195000 := bound_le_helper m 624 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 625 ≤ m := hm_gt
    have h1 : 195625 ≤ m*(m+1)/2 := bound_gt_helper m 625 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_630 (m : ℕ) (hm1 : m ≥ 1) : my_pi (630*631) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 630*631 = 397530 := by decide
  rw [hk_eq]
  have hk : my_pi (397530) = 33662 := pi_397530
  have hm0 : my_pi (193753) = 17475 := pi_193753
  have hm1_val : my_pi (194376) = 17525 := pi_194376
  rcases le_or_gt m 622 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 193753 := bound_le_helper m 622 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 623 ≤ m := hm_gt
    have h1 : 194376 ≤ m*(m+1)/2 := bound_gt_helper m 623 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_631 (m : ℕ) (hm1 : m ≥ 1) : my_pi (631*632) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 631*632 = 398792 := by decide
  rw [hk_eq]
  have hk : my_pi (398792) = 33764 := pi_398792
  have hm0 : my_pi (192510) = 17369 := pi_192510
  have hm1_val : my_pi (193131) = 17424 := pi_193131
  rcases le_or_gt m 620 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 192510 := bound_le_helper m 620 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 621 ≤ m := hm_gt
    have h1 : 193131 ≤ m*(m+1)/2 := bound_gt_helper m 621 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_632 (m : ℕ) (hm1 : m ≥ 1) : my_pi (632*633) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 632*633 = 400056 := by decide
  rw [hk_eq]
  have hk : my_pi (400056) = 33864 := pi_400056
  have hm0 : my_pi (191271) = 17267 := pi_191271
  have hm1_val : my_pi (191890) = 17318 := pi_191890
  rcases le_or_gt m 618 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 191271 := bound_le_helper m 618 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 619 ≤ m := hm_gt
    have h1 : 191890 ≤ m*(m+1)/2 := bound_gt_helper m 619 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_633 (m : ℕ) (hm1 : m ≥ 1) : my_pi (633*634) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 633*634 = 401322 := by decide
  rw [hk_eq]
  have hk : my_pi (401322) = 33954 := pi_401322
  have hm0 : my_pi (190036) = 17172 := pi_190036
  have hm1_val : my_pi (190653) = 17216 := pi_190653
  rcases le_or_gt m 616 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 190036 := bound_le_helper m 616 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 617 ≤ m := hm_gt
    have h1 : 190653 ≤ m*(m+1)/2 := bound_gt_helper m 617 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_634 (m : ℕ) (hm1 : m ≥ 1) : my_pi (634*635) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 634*635 = 402590 := by decide
  rw [hk_eq]
  have hk : my_pi (402590) = 34049 := pi_402590
  have hm0 : my_pi (188805) = 17064 := pi_188805
  have hm1_val : my_pi (189420) = 17115 := pi_189420
  rcases le_or_gt m 614 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 188805 := bound_le_helper m 614 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 615 ≤ m := hm_gt
    have h1 : 189420 ≤ m*(m+1)/2 := bound_gt_helper m 615 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_635 (m : ℕ) (hm1 : m ≥ 1) : my_pi (635*636) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 635*636 = 403860 := by decide
  rw [hk_eq]
  have hk : my_pi (403860) = 34140 := pi_403860
  have hm0 : my_pi (188191) = 17014 := pi_188191
  have hm1_val : my_pi (188805) = 17064 := pi_188805
  rcases le_or_gt m 613 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 188191 := bound_le_helper m 613 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 614 ≤ m := hm_gt
    have h1 : 188805 ≤ m*(m+1)/2 := bound_gt_helper m 614 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_636 (m : ℕ) (hm1 : m ≥ 1) : my_pi (636*637) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 636*637 = 405132 := by decide
  rw [hk_eq]
  have hk : my_pi (405132) = 34232 := pi_405132
  have hm0 : my_pi (186966) = 16915 := pi_186966
  have hm1_val : my_pi (187578) = 16970 := pi_187578
  rcases le_or_gt m 611 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 186966 := bound_le_helper m 611 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 612 ≤ m := hm_gt
    have h1 : 187578 ≤ m*(m+1)/2 := bound_gt_helper m 612 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_637 (m : ℕ) (hm1 : m ≥ 1) : my_pi (637*638) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 637*638 = 406406 := by decide
  rw [hk_eq]
  have hk : my_pi (406406) = 34332 := pi_406406
  have hm0 : my_pi (185745) = 16810 := pi_185745
  have hm1_val : my_pi (186355) = 16869 := pi_186355
  rcases le_or_gt m 609 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 185745 := bound_le_helper m 609 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 610 ≤ m := hm_gt
    have h1 : 186355 ≤ m*(m+1)/2 := bound_gt_helper m 610 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_638 (m : ℕ) (hm1 : m ≥ 1) : my_pi (638*639) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 638*639 = 407682 := by decide
  rw [hk_eq]
  have hk : my_pi (407682) = 34425 := pi_407682
  have hm0 : my_pi (184528) = 16706 := pi_184528
  have hm1_val : my_pi (185136) = 16757 := pi_185136
  rcases le_or_gt m 607 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 184528 := bound_le_helper m 607 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 608 ≤ m := hm_gt
    have h1 : 185136 ≤ m*(m+1)/2 := bound_gt_helper m 608 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_639 (m : ℕ) (hm1 : m ≥ 1) : my_pi (639*640) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 639*640 = 408960 := by decide
  rw [hk_eq]
  have hk : my_pi (408960) = 34529 := pi_408960
  have hm0 : my_pi (183315) = 16604 := pi_183315
  have hm1_val : my_pi (183921) = 16656 := pi_183921
  rcases le_or_gt m 605 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 183315 := bound_le_helper m 605 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 606 ≤ m := hm_gt
    have h1 : 183921 ≤ m*(m+1)/2 := bound_gt_helper m 606 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_640 (m : ℕ) (hm1 : m ≥ 1) : my_pi (640*641) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 640*641 = 410240 := by decide
  rw [hk_eq]
  have hk : my_pi (410240) = 34630 := pi_410240
  have hm0 : my_pi (182106) = 16503 := pi_182106
  have hm1_val : my_pi (182710) = 16558 := pi_182710
  rcases le_or_gt m 603 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 182106 := bound_le_helper m 603 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 604 ≤ m := hm_gt
    have h1 : 182710 ≤ m*(m+1)/2 := bound_gt_helper m 604 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_641 (m : ℕ) (hm1 : m ≥ 1) : my_pi (641*642) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 641*642 = 411522 := by decide
  rw [hk_eq]
  have hk : my_pi (411522) = 34728 := pi_411522
  have hm0 : my_pi (180901) = 16410 := pi_180901
  have hm1_val : my_pi (181503) = 16451 := pi_181503
  rcases le_or_gt m 601 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 180901 := bound_le_helper m 601 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 602 ≤ m := hm_gt
    have h1 : 181503 ≤ m*(m+1)/2 := bound_gt_helper m 602 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_642 (m : ℕ) (hm1 : m ≥ 1) : my_pi (642*643) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 642*643 = 412806 := by decide
  rw [hk_eq]
  have hk : my_pi (412806) = 34830 := pi_412806
  have hm0 : my_pi (179700) = 16313 := pi_179700
  have hm1_val : my_pi (180300) = 16366 := pi_180300
  rcases le_or_gt m 599 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 179700 := bound_le_helper m 599 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 600 ≤ m := hm_gt
    have h1 : 180300 ≤ m*(m+1)/2 := bound_gt_helper m 600 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_643 (m : ℕ) (hm1 : m ≥ 1) : my_pi (643*644) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 643*644 = 414092 := by decide
  rw [hk_eq]
  have hk : my_pi (414092) = 34920 := pi_414092
  have hm0 : my_pi (178503) = 16202 := pi_178503
  have hm1_val : my_pi (179101) = 16257 := pi_179101
  rcases le_or_gt m 597 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 178503 := bound_le_helper m 597 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 598 ≤ m := hm_gt
    have h1 : 179101 ≤ m*(m+1)/2 := bound_gt_helper m 598 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_644 (m : ℕ) (hm1 : m ≥ 1) : my_pi (644*645) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 644*645 = 415380 := by decide
  rw [hk_eq]
  have hk : my_pi (415380) = 35028 := pi_415380
  have hm0 : my_pi (177310) = 16108 := pi_177310
  have hm1_val : my_pi (177906) = 16150 := pi_177906
  rcases le_or_gt m 595 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 177310 := bound_le_helper m 595 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 596 ≤ m := hm_gt
    have h1 : 177906 ≤ m*(m+1)/2 := bound_gt_helper m 596 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_645 (m : ℕ) (hm1 : m ≥ 1) : my_pi (645*646) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 645*646 = 416670 := by decide
  rw [hk_eq]
  have hk : my_pi (416670) = 35131 := pi_416670
  have hm0 : my_pi (176121) = 16002 := pi_176121
  have hm1_val : my_pi (176715) = 16062 := pi_176715
  rcases le_or_gt m 593 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 176121 := bound_le_helper m 593 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 594 ≤ m := hm_gt
    have h1 : 176715 ≤ m*(m+1)/2 := bound_gt_helper m 594 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_646 (m : ℕ) (hm1 : m ≥ 1) : my_pi (646*647) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 646*647 = 417962 := by decide
  rw [hk_eq]
  have hk : my_pi (417962) = 35228 := pi_417962
  have hm0 : my_pi (174936) = 15912 := pi_174936
  have hm1_val : my_pi (175528) = 15952 := pi_175528
  rcases le_or_gt m 591 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 174936 := bound_le_helper m 591 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 592 ≤ m := hm_gt
    have h1 : 175528 ≤ m*(m+1)/2 := bound_gt_helper m 592 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_647 (m : ℕ) (hm1 : m ≥ 1) : my_pi (647*648) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 647*648 = 419256 := by decide
  rw [hk_eq]
  have hk : my_pi (419256) = 35331 := pi_419256
  have hm0 : my_pi (173755) = 15812 := pi_173755
  have hm1_val : my_pi (174345) = 15864 := pi_174345
  rcases le_or_gt m 589 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 173755 := bound_le_helper m 589 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 590 ≤ m := hm_gt
    have h1 : 174345 ≤ m*(m+1)/2 := bound_gt_helper m 590 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_648 (m : ℕ) (hm1 : m ≥ 1) : my_pi (648*649) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 648*649 = 420552 := by decide
  rw [hk_eq]
  have hk : my_pi (420552) = 35433 := pi_420552
  have hm0 : my_pi (172578) = 15716 := pi_172578
  have hm1_val : my_pi (173166) = 15765 := pi_173166
  rcases le_or_gt m 587 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 172578 := bound_le_helper m 587 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 588 ≤ m := hm_gt
    have h1 : 173166 ≤ m*(m+1)/2 := bound_gt_helper m 588 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_649 (m : ℕ) (hm1 : m ≥ 1) : my_pi (649*650) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 649*650 = 421850 := by decide
  rw [hk_eq]
  have hk : my_pi (421850) = 35531 := pi_421850
  have hm0 : my_pi (171405) = 15615 := pi_171405
  have hm1_val : my_pi (171991) = 15665 := pi_171991
  rcases le_or_gt m 585 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 171405 := bound_le_helper m 585 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 586 ≤ m := hm_gt
    have h1 : 171991 ≤ m*(m+1)/2 := bound_gt_helper m 586 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_650 (m : ℕ) (hm1 : m ≥ 1) : my_pi (650*651) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 650*651 = 423150 := by decide
  rw [hk_eq]
  have hk : my_pi (423150) = 35630 := pi_423150
  have hm0 : my_pi (170236) = 15517 := pi_170236
  have hm1_val : my_pi (170820) = 15570 := pi_170820
  rcases le_or_gt m 583 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 170236 := bound_le_helper m 583 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 584 ≤ m := hm_gt
    have h1 : 170820 ≤ m*(m+1)/2 := bound_gt_helper m 584 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_651 (m : ℕ) (hm1 : m ≥ 1) : my_pi (651*652) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 651*652 = 424452 := by decide
  rw [hk_eq]
  have hk : my_pi (424452) = 35736 := pi_424452
  have hm0 : my_pi (169071) = 15418 := pi_169071
  have hm1_val : my_pi (169653) = 15465 := pi_169653
  rcases le_or_gt m 581 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 169071 := bound_le_helper m 581 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 582 ≤ m := hm_gt
    have h1 : 169653 ≤ m*(m+1)/2 := bound_gt_helper m 582 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_652 (m : ℕ) (hm1 : m ≥ 1) : my_pi (652*653) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 652*653 = 425756 := by decide
  rw [hk_eq]
  have hk : my_pi (425756) = 35832 := pi_425756
  have hm0 : my_pi (167331) = 15287 := pi_167331
  have hm1_val : my_pi (167910) = 15332 := pi_167910
  rcases le_or_gt m 578 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 167331 := bound_le_helper m 578 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 579 ≤ m := hm_gt
    have h1 : 167910 ≤ m*(m+1)/2 := bound_gt_helper m 579 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_653 (m : ℕ) (hm1 : m ≥ 1) : my_pi (653*654) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 653*654 = 427062 := by decide
  rw [hk_eq]
  have hk : my_pi (427062) = 35928 := pi_427062
  have hm0 : my_pi (166176) = 15185 := pi_166176
  have hm1_val : my_pi (166753) = 15233 := pi_166753
  rcases le_or_gt m 576 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 166176 := bound_le_helper m 576 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 577 ≤ m := hm_gt
    have h1 : 166753 ≤ m*(m+1)/2 := bound_gt_helper m 577 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_654 (m : ℕ) (hm1 : m ≥ 1) : my_pi (654*655) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 654*655 = 428370 := by decide
  rw [hk_eq]
  have hk : my_pi (428370) = 36031 := pi_428370
  have hm0 : my_pi (165025) = 15094 := pi_165025
  have hm1_val : my_pi (165600) = 15143 := pi_165600
  rcases le_or_gt m 574 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 165025 := bound_le_helper m 574 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 575 ≤ m := hm_gt
    have h1 : 165600 ≤ m*(m+1)/2 := bound_gt_helper m 575 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_655 (m : ℕ) (hm1 : m ≥ 1) : my_pi (655*656) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 655*656 = 429680 := by decide
  rw [hk_eq]
  have hk : my_pi (429680) = 36132 := pi_429680
  have hm0 : my_pi (163878) = 15005 := pi_163878
  have hm1_val : my_pi (164451) = 15057 := pi_164451
  rcases le_or_gt m 572 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 163878 := bound_le_helper m 572 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 573 ≤ m := hm_gt
    have h1 : 164451 ≤ m*(m+1)/2 := bound_gt_helper m 573 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_656 (m : ℕ) (hm1 : m ≥ 1) : my_pi (656*657) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 656*657 = 430992 := by decide
  rw [hk_eq]
  have hk : my_pi (430992) = 36237 := pi_430992
  have hm0 : my_pi (162735) = 14909 := pi_162735
  have hm1_val : my_pi (163306) = 14955 := pi_163306
  rcases le_or_gt m 570 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 162735 := bound_le_helper m 570 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 571 ≤ m := hm_gt
    have h1 : 163306 ≤ m*(m+1)/2 := bound_gt_helper m 571 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_657 (m : ℕ) (hm1 : m ≥ 1) : my_pi (657*658) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 657*658 = 432306 := by decide
  rw [hk_eq]
  have hk : my_pi (432306) = 36345 := pi_432306
  have hm0 : my_pi (161028) = 14770 := pi_161028
  have hm1_val : my_pi (161596) = 14817 := pi_161596
  rcases le_or_gt m 567 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 161028 := bound_le_helper m 567 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 568 ≤ m := hm_gt
    have h1 : 161596 ≤ m*(m+1)/2 := bound_gt_helper m 568 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_658 (m : ℕ) (hm1 : m ≥ 1) : my_pi (658*659) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 658*659 = 433622 := by decide
  rw [hk_eq]
  have hk : my_pi (433622) = 36451 := pi_433622
  have hm0 : my_pi (159895) = 14677 := pi_159895
  have hm1_val : my_pi (160461) = 14721 := pi_160461
  rcases le_or_gt m 565 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 159895 := bound_le_helper m 565 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 566 ≤ m := hm_gt
    have h1 : 160461 ≤ m*(m+1)/2 := bound_gt_helper m 566 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_659 (m : ℕ) (hm1 : m ≥ 1) : my_pi (659*660) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 659*660 = 434940 := by decide
  rw [hk_eq]
  have hk : my_pi (434940) = 36560 := pi_434940
  have hm0 : my_pi (158766) = 14582 := pi_158766
  have hm1_val : my_pi (159330) = 14623 := pi_159330
  rcases le_or_gt m 563 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 158766 := bound_le_helper m 563 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 564 ≤ m := hm_gt
    have h1 : 159330 ≤ m*(m+1)/2 := bound_gt_helper m 564 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_660 (m : ℕ) (hm1 : m ≥ 1) : my_pi (660*661) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 660*661 = 436260 := by decide
  rw [hk_eq]
  have hk : my_pi (436260) = 36665 := pi_436260
  have hm0 : my_pi (157080) = 14441 := pi_157080
  have hm1_val : my_pi (157641) = 14493 := pi_157641
  rcases le_or_gt m 560 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 157080 := bound_le_helper m 560 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 561 ≤ m := hm_gt
    have h1 : 157641 ≤ m*(m+1)/2 := bound_gt_helper m 561 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_661 (m : ℕ) (hm1 : m ≥ 1) : my_pi (661*662) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 661*662 = 437582 := by decide
  rw [hk_eq]
  have hk : my_pi (437582) = 36764 := pi_437582
  have hm0 : my_pi (155961) = 14357 := pi_155961
  have hm1_val : my_pi (156520) = 14395 := pi_156520
  rcases le_or_gt m 558 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 155961 := bound_le_helper m 558 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 559 ≤ m := hm_gt
    have h1 : 156520 ≤ m*(m+1)/2 := bound_gt_helper m 559 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_662 (m : ℕ) (hm1 : m ≥ 1) : my_pi (662*663) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 662*663 = 438906 := by decide
  rw [hk_eq]
  have hk : my_pi (438906) = 36857 := pi_438906
  have hm0 : my_pi (154846) = 14260 := pi_154846
  have hm1_val : my_pi (155403) = 14307 := pi_155403
  rcases le_or_gt m 556 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 154846 := bound_le_helper m 556 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 557 ≤ m := hm_gt
    have h1 : 155403 ≤ m*(m+1)/2 := bound_gt_helper m 557 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_663 (m : ℕ) (hm1 : m ≥ 1) : my_pi (663*664) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 663*664 = 440232 := by decide
  rw [hk_eq]
  have hk : my_pi (440232) = 36958 := pi_440232
  have hm0 : my_pi (153735) = 14168 := pi_153735
  have hm1_val : my_pi (154290) = 14214 := pi_154290
  rcases le_or_gt m 554 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 153735 := bound_le_helper m 554 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 555 ≤ m := hm_gt
    have h1 : 154290 ≤ m*(m+1)/2 := bound_gt_helper m 555 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_664 (m : ℕ) (hm1 : m ≥ 1) : my_pi (664*665) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 664*665 = 441560 := by decide
  rw [hk_eq]
  have hk : my_pi (441560) = 37062 := pi_441560
  have hm0 : my_pi (152628) = 14076 := pi_152628
  have hm1_val : my_pi (153181) = 14123 := pi_153181
  rcases le_or_gt m 552 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 152628 := bound_le_helper m 552 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 553 ≤ m := hm_gt
    have h1 : 153181 ≤ m*(m+1)/2 := bound_gt_helper m 553 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_665 (m : ℕ) (hm1 : m ≥ 1) : my_pi (665*666) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 665*666 = 442890 := by decide
  rw [hk_eq]
  have hk : my_pi (442890) = 37168 := pi_442890
  have hm0 : my_pi (151525) = 13979 := pi_151525
  have hm1_val : my_pi (152076) = 14030 := pi_152076
  rcases le_or_gt m 550 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 151525 := bound_le_helper m 550 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 551 ≤ m := hm_gt
    have h1 : 152076 ≤ m*(m+1)/2 := bound_gt_helper m 551 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_666 (m : ℕ) (hm1 : m ≥ 1) : my_pi (666*667) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 666*667 = 444222 := by decide
  rw [hk_eq]
  have hk : my_pi (444222) = 37284 := pi_444222
  have hm0 : my_pi (149878) = 13838 := pi_149878
  have hm1_val : my_pi (150426) = 13886 := pi_150426
  rcases le_or_gt m 547 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 149878 := bound_le_helper m 547 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 548 ≤ m := hm_gt
    have h1 : 150426 ≤ m*(m+1)/2 := bound_gt_helper m 548 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_667 (m : ℕ) (hm1 : m ≥ 1) : my_pi (667*668) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 667*668 = 445556 := by decide
  rw [hk_eq]
  have hk : my_pi (445556) = 37383 := pi_445556
  have hm0 : my_pi (148785) = 13738 := pi_148785
  have hm1_val : my_pi (149331) = 13789 := pi_149331
  rcases le_or_gt m 545 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 148785 := bound_le_helper m 545 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 546 ≤ m := hm_gt
    have h1 : 149331 ≤ m*(m+1)/2 := bound_gt_helper m 546 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_668 (m : ℕ) (hm1 : m ≥ 1) : my_pi (668*669) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 668*669 = 446892 := by decide
  rw [hk_eq]
  have hk : my_pi (446892) = 37475 := pi_446892
  have hm0 : my_pi (147696) = 13651 := pi_147696
  have hm1_val : my_pi (148240) = 13693 := pi_148240
  rcases le_or_gt m 543 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 147696 := bound_le_helper m 543 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 544 ≤ m := hm_gt
    have h1 : 148240 ≤ m*(m+1)/2 := bound_gt_helper m 544 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_669 (m : ℕ) (hm1 : m ≥ 1) : my_pi (669*670) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 669*670 = 448230 := by decide
  rw [hk_eq]
  have hk : my_pi (448230) = 37576 := pi_448230
  have hm0 : my_pi (146611) = 13559 := pi_146611
  have hm1_val : my_pi (147153) = 13603 := pi_147153
  rcases le_or_gt m 541 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 146611 := bound_le_helper m 541 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 542 ≤ m := hm_gt
    have h1 : 147153 ≤ m*(m+1)/2 := bound_gt_helper m 542 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_670 (m : ℕ) (hm1 : m ≥ 1) : my_pi (670*671) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 670*671 = 449570 := by decide
  rw [hk_eq]
  have hk : my_pi (449570) = 37674 := pi_449570
  have hm0 : my_pi (145530) = 13466 := pi_145530
  have hm1_val : my_pi (146070) = 13516 := pi_146070
  rcases le_or_gt m 539 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 145530 := bound_le_helper m 539 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 540 ≤ m := hm_gt
    have h1 : 146070 ≤ m*(m+1)/2 := bound_gt_helper m 540 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_671 (m : ℕ) (hm1 : m ≥ 1) : my_pi (671*672) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 671*672 = 450912 := by decide
  rw [hk_eq]
  have hk : my_pi (450912) = 37790 := pi_450912
  have hm0 : my_pi (143916) = 13337 := pi_143916
  have hm1_val : my_pi (144453) = 13378 := pi_144453
  rcases le_or_gt m 536 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 143916 := bound_le_helper m 536 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 537 ≤ m := hm_gt
    have h1 : 144453 ≤ m*(m+1)/2 := bound_gt_helper m 537 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_672 (m : ℕ) (hm1 : m ≥ 1) : my_pi (672*673) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 672*673 = 452256 := by decide
  rw [hk_eq]
  have hk : my_pi (452256) = 37892 := pi_452256
  have hm0 : my_pi (142845) = 13252 := pi_142845
  have hm1_val : my_pi (143380) = 13289 := pi_143380
  rcases le_or_gt m 534 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 142845 := bound_le_helper m 534 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 535 ≤ m := hm_gt
    have h1 : 143380 ≤ m*(m+1)/2 := bound_gt_helper m 535 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_673 (m : ℕ) (hm1 : m ≥ 1) : my_pi (673*674) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 673*674 = 453602 := by decide
  rw [hk_eq]
  have hk : my_pi (453602) = 37978 := pi_453602
  have hm0 : my_pi (141778) = 13166 := pi_141778
  have hm1_val : my_pi (142311) = 13210 := pi_142311
  rcases le_or_gt m 532 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 141778 := bound_le_helper m 532 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 533 ≤ m := hm_gt
    have h1 : 142311 ≤ m*(m+1)/2 := bound_gt_helper m 533 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_674 (m : ℕ) (hm1 : m ≥ 1) : my_pi (674*675) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 674*675 = 454950 := by decide
  rw [hk_eq]
  have hk : my_pi (454950) = 38079 := pi_454950
  have hm0 : my_pi (140715) = 13071 := pi_140715
  have hm1_val : my_pi (141246) = 13117 := pi_141246
  rcases le_or_gt m 530 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 140715 := bound_le_helper m 530 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 531 ≤ m := hm_gt
    have h1 : 141246 ≤ m*(m+1)/2 := bound_gt_helper m 531 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_675 (m : ℕ) (hm1 : m ≥ 1) : my_pi (675*676) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 675*676 = 456300 := by decide
  rw [hk_eq]
  have hk : my_pi (456300) = 38184 := pi_456300
  have hm0 : my_pi (139128) = 12934 := pi_139128
  have hm1_val : my_pi (139656) = 12978 := pi_139656
  rcases le_or_gt m 527 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 139128 := bound_le_helper m 527 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 528 ≤ m := hm_gt
    have h1 : 139656 ≤ m*(m+1)/2 := bound_gt_helper m 528 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_676 (m : ℕ) (hm1 : m ≥ 1) : my_pi (676*677) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 676*677 = 457652 := by decide
  rw [hk_eq]
  have hk : my_pi (457652) = 38292 := pi_457652
  have hm0 : my_pi (138075) = 12846 := pi_138075
  have hm1_val : my_pi (138601) = 12896 := pi_138601
  rcases le_or_gt m 525 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 138075 := bound_le_helper m 525 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 526 ≤ m := hm_gt
    have h1 : 138601 ≤ m*(m+1)/2 := bound_gt_helper m 526 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_677 (m : ℕ) (hm1 : m ≥ 1) : my_pi (677*678) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 677*678 = 459006 := by decide
  rw [hk_eq]
  have hk : my_pi (459006) = 38390 := pi_459006
  have hm0 : my_pi (137026) = 12761 := pi_137026
  have hm1_val : my_pi (137550) = 12805 := pi_137550
  rcases le_or_gt m 523 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 137026 := bound_le_helper m 523 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 524 ≤ m := hm_gt
    have h1 : 137550 ≤ m*(m+1)/2 := bound_gt_helper m 524 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_678 (m : ℕ) (hm1 : m ≥ 1) : my_pi (678*679) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 678*679 = 460362 := by decide
  rw [hk_eq]
  have hk : my_pi (460362) = 38485 := pi_460362
  have hm0 : my_pi (135981) = 12665 := pi_135981
  have hm1_val : my_pi (136503) = 12714 := pi_136503
  rcases le_or_gt m 521 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 135981 := bound_le_helper m 521 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 522 ≤ m := hm_gt
    have h1 : 136503 ≤ m*(m+1)/2 := bound_gt_helper m 522 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_679 (m : ℕ) (hm1 : m ≥ 1) : my_pi (679*680) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 679*680 = 461720 := by decide
  rw [hk_eq]
  have hk : my_pi (461720) = 38590 := pi_461720
  have hm0 : my_pi (134421) = 12535 := pi_134421
  have hm1_val : my_pi (134940) = 12572 := pi_134940
  rcases le_or_gt m 518 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 134421 := bound_le_helper m 518 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 519 ≤ m := hm_gt
    have h1 : 134940 ≤ m*(m+1)/2 := bound_gt_helper m 519 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_680 (m : ℕ) (hm1 : m ≥ 1) : my_pi (680*681) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 680*681 = 463080 := by decide
  rw [hk_eq]
  have hk : my_pi (463080) = 38681 := pi_463080
  have hm0 : my_pi (133386) = 12448 := pi_133386
  have hm1_val : my_pi (133903) = 12488 := pi_133903
  rcases le_or_gt m 516 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 133386 := bound_le_helper m 516 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 517 ≤ m := hm_gt
    have h1 : 133903 ≤ m*(m+1)/2 := bound_gt_helper m 517 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_681 (m : ℕ) (hm1 : m ≥ 1) : my_pi (681*682) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 681*682 = 464442 := by decide
  rw [hk_eq]
  have hk : my_pi (464442) = 38791 := pi_464442
  have hm0 : my_pi (132355) = 12355 := pi_132355
  have hm1_val : my_pi (132870) = 12403 := pi_132870
  rcases le_or_gt m 514 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 132355 := bound_le_helper m 514 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 515 ≤ m := hm_gt
    have h1 : 132870 ≤ m*(m+1)/2 := bound_gt_helper m 515 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_682 (m : ℕ) (hm1 : m ≥ 1) : my_pi (682*683) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 682*683 = 465806 := by decide
  rw [hk_eq]
  have hk : my_pi (465806) = 38901 := pi_465806
  have hm0 : my_pi (130816) = 12232 := pi_130816
  have hm1_val : my_pi (131328) = 12271 := pi_131328
  rcases le_or_gt m 511 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 130816 := bound_le_helper m 511 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 512 ≤ m := hm_gt
    have h1 : 131328 ≤ m*(m+1)/2 := bound_gt_helper m 512 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_683 (m : ℕ) (hm1 : m ≥ 1) : my_pi (683*684) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 683*684 = 467172 := by decide
  rw [hk_eq]
  have hk : my_pi (467172) = 38996 := pi_467172
  have hm0 : my_pi (129795) = 12146 := pi_129795
  have hm1_val : my_pi (130305) = 12186 := pi_130305
  rcases le_or_gt m 509 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 129795 := bound_le_helper m 509 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 510 ≤ m := hm_gt
    have h1 : 130305 ≤ m*(m+1)/2 := bound_gt_helper m 510 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_684 (m : ℕ) (hm1 : m ≥ 1) : my_pi (684*685) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 684*685 = 468540 := by decide
  rw [hk_eq]
  have hk : my_pi (468540) = 39109 := pi_468540
  have hm0 : my_pi (128271) = 12007 := pi_128271
  have hm1_val : my_pi (128778) = 12055 := pi_128778
  rcases le_or_gt m 506 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 128271 := bound_le_helper m 506 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 507 ≤ m := hm_gt
    have h1 : 128778 ≤ m*(m+1)/2 := bound_gt_helper m 507 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_685 (m : ℕ) (hm1 : m ≥ 1) : my_pi (685*686) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 685*686 = 469910 := by decide
  rw [hk_eq]
  have hk : my_pi (469910) = 39217 := pi_469910
  have hm0 : my_pi (127260) = 11920 := pi_127260
  have hm1_val : my_pi (127765) = 11969 := pi_127765
  rcases le_or_gt m 504 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 127260 := bound_le_helper m 504 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 505 ≤ m := hm_gt
    have h1 : 127765 ≤ m*(m+1)/2 := bound_gt_helper m 505 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_686 (m : ℕ) (hm1 : m ≥ 1) : my_pi (686*687) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 686*687 = 471282 := by decide
  rw [hk_eq]
  have hk : my_pi (471282) = 39331 := pi_471282
  have hm0 : my_pi (125751) = 11800 := pi_125751
  have hm1_val : my_pi (126253) = 11843 := pi_126253
  rcases le_or_gt m 501 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 125751 := bound_le_helper m 501 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 502 ≤ m := hm_gt
    have h1 : 126253 ≤ m*(m+1)/2 := bound_gt_helper m 502 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_687 (m : ℕ) (hm1 : m ≥ 1) : my_pi (687*688) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 687*688 = 472656 := by decide
  rw [hk_eq]
  have hk : my_pi (472656) = 39436 := pi_472656
  have hm0 : my_pi (124750) = 11712 := pi_124750
  have hm1_val : my_pi (125250) = 11756 := pi_125250
  rcases le_or_gt m 499 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 124750 := bound_le_helper m 499 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 500 ≤ m := hm_gt
    have h1 : 125250 ≤ m*(m+1)/2 := bound_gt_helper m 500 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_688 (m : ℕ) (hm1 : m ≥ 1) : my_pi (688*689) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 688*689 = 474032 := by decide
  rw [hk_eq]
  have hk : my_pi (474032) = 39541 := pi_474032
  have hm0 : my_pi (123256) = 11583 := pi_123256
  have hm1_val : my_pi (123753) = 11630 := pi_123753
  rcases le_or_gt m 496 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 123256 := bound_le_helper m 496 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 497 ≤ m := hm_gt
    have h1 : 123753 ≤ m*(m+1)/2 := bound_gt_helper m 497 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_689 (m : ℕ) (hm1 : m ≥ 1) : my_pi (689*690) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 689*690 = 475410 := by decide
  rw [hk_eq]
  have hk : my_pi (475410) = 39651 := pi_475410
  have hm0 : my_pi (122265) = 11501 := pi_122265
  have hm1_val : my_pi (122760) = 11543 := pi_122760
  rcases le_or_gt m 494 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 122265 := bound_le_helper m 494 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 495 ≤ m := hm_gt
    have h1 : 122760 ≤ m*(m+1)/2 := bound_gt_helper m 495 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_690 (m : ℕ) (hm1 : m ≥ 1) : my_pi (690*691) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 690*691 = 476790 := by decide
  rw [hk_eq]
  have hk : my_pi (476790) = 39766 := pi_476790
  have hm0 : my_pi (120786) = 11367 := pi_120786
  have hm1_val : my_pi (121278) = 11411 := pi_121278
  rcases le_or_gt m 491 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 120786 := bound_le_helper m 491 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 492 ≤ m := hm_gt
    have h1 : 121278 ≤ m*(m+1)/2 := bound_gt_helper m 492 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_691 (m : ℕ) (hm1 : m ≥ 1) : my_pi (691*692) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 691*692 = 478172 := by decide
  rw [hk_eq]
  have hk : my_pi (478172) = 39862 := pi_478172
  have hm0 : my_pi (119805) = 11282 := pi_119805
  have hm1_val : my_pi (120295) = 11326 := pi_120295
  rcases le_or_gt m 489 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 119805 := bound_le_helper m 489 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 490 ≤ m := hm_gt
    have h1 : 120295 ≤ m*(m+1)/2 := bound_gt_helper m 490 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_692 (m : ℕ) (hm1 : m ≥ 1) : my_pi (692*693) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 692*693 = 479556 := by decide
  rw [hk_eq]
  have hk : my_pi (479556) = 39974 := pi_479556
  have hm0 : my_pi (118341) = 11159 := pi_118341
  have hm1_val : my_pi (118828) = 11200 := pi_118828
  rcases le_or_gt m 486 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 118341 := bound_le_helper m 486 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 487 ≤ m := hm_gt
    have h1 : 118828 ≤ m*(m+1)/2 := bound_gt_helper m 487 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_693 (m : ℕ) (hm1 : m ≥ 1) : my_pi (693*694) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 693*694 = 480942 := by decide
  rw [hk_eq]
  have hk : my_pi (480942) = 40078 := pi_480942
  have hm0 : my_pi (117370) = 11076 := pi_117370
  have hm1_val : my_pi (117855) = 11121 := pi_117855
  rcases le_or_gt m 484 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 117370 := bound_le_helper m 484 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 485 ≤ m := hm_gt
    have h1 : 117855 ≤ m*(m+1)/2 := bound_gt_helper m 485 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_694 (m : ℕ) (hm1 : m ≥ 1) : my_pi (694*695) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 694*695 = 482330 := by decide
  rw [hk_eq]
  have hk : my_pi (482330) = 40184 := pi_482330
  have hm0 : my_pi (115921) = 10958 := pi_115921
  have hm1_val : my_pi (116403) = 10995 := pi_116403
  rcases le_or_gt m 481 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 115921 := bound_le_helper m 481 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 482 ≤ m := hm_gt
    have h1 : 116403 ≤ m*(m+1)/2 := bound_gt_helper m 482 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_695 (m : ℕ) (hm1 : m ≥ 1) : my_pi (695*696) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 695*696 = 483720 := by decide
  rw [hk_eq]
  have hk : my_pi (483720) = 40294 := pi_483720
  have hm0 : my_pi (114481) = 10828 := pi_114481
  have hm1_val : my_pi (114960) = 10868 := pi_114960
  rcases le_or_gt m 478 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 114481 := bound_le_helper m 478 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 479 ≤ m := hm_gt
    have h1 : 114960 ≤ m*(m+1)/2 := bound_gt_helper m 479 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_696 (m : ℕ) (hm1 : m ≥ 1) : my_pi (696*697) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 696*697 = 485112 := by decide
  rw [hk_eq]
  have hk : my_pi (485112) = 40390 := pi_485112
  have hm0 : my_pi (113526) = 10752 := pi_113526
  have hm1_val : my_pi (114003) = 10790 := pi_114003
  rcases le_or_gt m 476 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 113526 := bound_le_helper m 476 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 477 ≤ m := hm_gt
    have h1 : 114003 ≤ m*(m+1)/2 := bound_gt_helper m 477 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_697 (m : ℕ) (hm1 : m ≥ 1) : my_pi (697*698) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 697*698 = 486506 := by decide
  rw [hk_eq]
  have hk : my_pi (486506) = 40486 := pi_486506
  have hm0 : my_pi (112575) = 10668 := pi_112575
  have hm1_val : my_pi (113050) = 10708 := pi_113050
  rcases le_or_gt m 474 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 112575 := bound_le_helper m 474 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 475 ≤ m := hm_gt
    have h1 : 113050 ≤ m*(m+1)/2 := bound_gt_helper m 475 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_698 (m : ℕ) (hm1 : m ≥ 1) : my_pi (698*699) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 698*699 = 487902 := by decide
  rw [hk_eq]
  have hk : my_pi (487902) = 40600 := pi_487902
  have hm0 : my_pi (111156) = 10549 := pi_111156
  have hm1_val : my_pi (111628) = 10586 := pi_111628
  rcases le_or_gt m 471 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 111156 := bound_le_helper m 471 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 472 ≤ m := hm_gt
    have h1 : 111628 ≤ m*(m+1)/2 := bound_gt_helper m 472 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_699 (m : ℕ) (hm1 : m ≥ 1) : my_pi (699*700) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 699*700 = 489300 := by decide
  rw [hk_eq]
  have hk : my_pi (489300) = 40711 := pi_489300
  have hm0 : my_pi (109746) = 10430 := pi_109746
  have hm1_val : my_pi (110215) = 10465 := pi_110215
  rcases le_or_gt m 468 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 109746 := bound_le_helper m 468 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 469 ≤ m := hm_gt
    have h1 : 110215 ≤ m*(m+1)/2 := bound_gt_helper m 469 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_700 (m : ℕ) (hm1 : m ≥ 1) : my_pi (700*701) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 700*701 = 490700 := by decide
  rw [hk_eq]
  have hk : my_pi (490700) = 40822 := pi_490700
  have hm0 : my_pi (108345) = 10306 := pi_108345
  have hm1_val : my_pi (108811) = 10344 := pi_108811
  rcases le_or_gt m 465 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 108345 := bound_le_helper m 465 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 466 ≤ m := hm_gt
    have h1 : 108811 ≤ m*(m+1)/2 := bound_gt_helper m 466 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_701 (m : ℕ) (hm1 : m ≥ 1) : my_pi (701*702) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 701*702 = 492102 := by decide
  rw [hk_eq]
  have hk : my_pi (492102) = 40931 := pi_492102
  have hm0 : my_pi (106953) = 10193 := pi_106953
  have hm1_val : my_pi (107416) = 10229 := pi_107416
  rcases le_or_gt m 462 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 106953 := bound_le_helper m 462 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 463 ≤ m := hm_gt
    have h1 : 107416 ≤ m*(m+1)/2 := bound_gt_helper m 463 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_702 (m : ℕ) (hm1 : m ≥ 1) : my_pi (702*703) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 702*703 = 493506 := by decide
  rw [hk_eq]
  have hk : my_pi (493506) = 41031 := pi_493506
  have hm0 : my_pi (106030) = 10108 := pi_106030
  have hm1_val : my_pi (106491) = 10151 := pi_106491
  rcases le_or_gt m 460 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 106030 := bound_le_helper m 460 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 461 ≤ m := hm_gt
    have h1 : 106491 ≤ m*(m+1)/2 := bound_gt_helper m 461 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_703 (m : ℕ) (hm1 : m ≥ 1) : my_pi (703*704) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 703*704 = 494912 := by decide
  rw [hk_eq]
  have hk : my_pi (494912) = 41143 := pi_494912
  have hm0 : my_pi (104653) = 9989 := pi_104653
  have hm1_val : my_pi (105111) = 10031 := pi_105111
  rcases le_or_gt m 457 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 104653 := bound_le_helper m 457 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 458 ≤ m := hm_gt
    have h1 : 105111 ≤ m*(m+1)/2 := bound_gt_helper m 458 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_704 (m : ℕ) (hm1 : m ≥ 1) : my_pi (704*705) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 704*705 = 496320 := by decide
  rw [hk_eq]
  have hk : my_pi (496320) = 41258 := pi_496320
  have hm0 : my_pi (103285) = 9872 := pi_103285
  have hm1_val : my_pi (103740) = 9911 := pi_103740
  rcases le_or_gt m 454 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 103285 := bound_le_helper m 454 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 455 ≤ m := hm_gt
    have h1 : 103740 ≤ m*(m+1)/2 := bound_gt_helper m 455 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_705 (m : ℕ) (hm1 : m ≥ 1) : my_pi (705*706) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 705*706 = 497730 := by decide
  rw [hk_eq]
  have hk : my_pi (497730) = 41364 := pi_497730
  have hm0 : my_pi (101926) = 9759 := pi_101926
  have hm1_val : my_pi (102378) = 9804 := pi_102378
  rcases le_or_gt m 451 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 101926 := bound_le_helper m 451 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 452 ≤ m := hm_gt
    have h1 : 102378 ≤ m*(m+1)/2 := bound_gt_helper m 452 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_706 (m : ℕ) (hm1 : m ≥ 1) : my_pi (706*707) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 706*707 = 499142 := by decide
  rw [hk_eq]
  have hk : my_pi (499142) = 41470 := pi_499142
  have hm0 : my_pi (101025) = 9675 := pi_101025
  have hm1_val : my_pi (101475) = 9716 := pi_101475
  rcases le_or_gt m 449 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 101025 := bound_le_helper m 449 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 450 ≤ m := hm_gt
    have h1 : 101475 ≤ m*(m+1)/2 := bound_gt_helper m 450 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_707 (m : ℕ) (hm1 : m ≥ 1) : my_pi (707*708) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 707*708 = 500556 := by decide
  rw [hk_eq]
  have hk : my_pi (500556) = 41583 := pi_500556
  have hm0 : my_pi (99681) = 9563 := pi_99681
  have hm1_val : my_pi (100128) = 9600 := pi_100128
  rcases le_or_gt m 446 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 99681 := bound_le_helper m 446 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 447 ≤ m := hm_gt
    have h1 : 100128 ≤ m*(m+1)/2 := bound_gt_helper m 447 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_708 (m : ℕ) (hm1 : m ≥ 1) : my_pi (708*709) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 708*709 = 501972 := by decide
  rw [hk_eq]
  have hk : my_pi (501972) = 41690 := pi_501972
  have hm0 : my_pi (98346) = 9443 := pi_98346
  have hm1_val : my_pi (98790) = 9482 := pi_98790
  rcases le_or_gt m 443 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 98346 := bound_le_helper m 443 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 444 ≤ m := hm_gt
    have h1 : 98790 ≤ m*(m+1)/2 := bound_gt_helper m 444 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_709 (m : ℕ) (hm1 : m ≥ 1) : my_pi (709*710) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 709*710 = 503390 := by decide
  rw [hk_eq]
  have hk : my_pi (503390) = 41787 := pi_503390
  have hm0 : my_pi (97020) = 9339 := pi_97020
  have hm1_val : my_pi (97461) = 9373 := pi_97461
  rcases le_or_gt m 440 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 97020 := bound_le_helper m 440 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 441 ≤ m := hm_gt
    have h1 : 97461 ≤ m*(m+1)/2 := bound_gt_helper m 441 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_710 (m : ℕ) (hm1 : m ≥ 1) : my_pi (710*711) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 710*711 = 504810 := by decide
  rw [hk_eq]
  have hk : my_pi (504810) = 41892 := pi_504810
  have hm0 : my_pi (96141) = 9261 := pi_96141
  have hm1_val : my_pi (96580) = 9299 := pi_96580
  rcases le_or_gt m 438 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 96141 := bound_le_helper m 438 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 439 ≤ m := hm_gt
    have h1 : 96580 ≤ m*(m+1)/2 := bound_gt_helper m 439 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_711 (m : ℕ) (hm1 : m ≥ 1) : my_pi (711*712) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 711*712 = 506232 := by decide
  rw [hk_eq]
  have hk : my_pi (506232) = 42006 := pi_506232
  have hm0 : my_pi (94830) = 9143 := pi_94830
  have hm1_val : my_pi (95266) = 9184 := pi_95266
  rcases le_or_gt m 435 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 94830 := bound_le_helper m 435 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 436 ≤ m := hm_gt
    have h1 : 95266 ≤ m*(m+1)/2 := bound_gt_helper m 436 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_712 (m : ℕ) (hm1 : m ≥ 1) : my_pi (712*713) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 712*713 = 507656 := by decide
  rw [hk_eq]
  have hk : my_pi (507656) = 42114 := pi_507656
  have hm0 : my_pi (93528) = 9032 := pi_93528
  have hm1_val : my_pi (93961) = 9065 := pi_93961
  rcases le_or_gt m 432 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 93528 := bound_le_helper m 432 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 433 ≤ m := hm_gt
    have h1 : 93961 ≤ m*(m+1)/2 := bound_gt_helper m 433 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_713 (m : ℕ) (hm1 : m ≥ 1) : my_pi (713*714) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 713*714 = 509082 := by decide
  rw [hk_eq]
  have hk : my_pi (509082) = 42221 := pi_509082
  have hm0 : my_pi (92235) = 8908 := pi_92235
  have hm1_val : my_pi (92665) = 8949 := pi_92665
  rcases le_or_gt m 429 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 92235 := bound_le_helper m 429 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 430 ≤ m := hm_gt
    have h1 : 92665 ≤ m*(m+1)/2 := bound_gt_helper m 430 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_714 (m : ℕ) (hm1 : m ≥ 1) : my_pi (714*715) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 714*715 = 510510 := by decide
  rw [hk_eq]
  have hk : my_pi (510510) = 42331 := pi_510510
  have hm0 : my_pi (90951) = 8798 := pi_90951
  have hm1_val : my_pi (91378) = 8835 := pi_91378
  rcases le_or_gt m 426 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 90951 := bound_le_helper m 426 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 427 ≤ m := hm_gt
    have h1 : 91378 ≤ m*(m+1)/2 := bound_gt_helper m 427 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_715 (m : ℕ) (hm1 : m ≥ 1) : my_pi (715*716) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 715*716 = 511940 := by decide
  rw [hk_eq]
  have hk : my_pi (511940) = 42441 := pi_511940
  have hm0 : my_pi (89676) = 8686 := pi_89676
  have hm1_val : my_pi (90100) = 8726 := pi_90100
  rcases le_or_gt m 423 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 89676 := bound_le_helper m 423 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 424 ≤ m := hm_gt
    have h1 : 90100 ≤ m*(m+1)/2 := bound_gt_helper m 424 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_716 (m : ℕ) (hm1 : m ≥ 1) : my_pi (716*717) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 716*717 = 513372 := by decide
  rw [hk_eq]
  have hk : my_pi (513372) = 42549 := pi_513372
  have hm0 : my_pi (88831) = 8605 := pi_88831
  have hm1_val : my_pi (89253) = 8644 := pi_89253
  rcases le_or_gt m 421 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 88831 := bound_le_helper m 421 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 422 ≤ m := hm_gt
    have h1 : 89253 ≤ m*(m+1)/2 := bound_gt_helper m 422 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_717 (m : ℕ) (hm1 : m ≥ 1) : my_pi (717*718) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 717*718 = 514806 := by decide
  rw [hk_eq]
  have hk : my_pi (514806) = 42658 := pi_514806
  have hm0 : my_pi (87153) = 8464 := pi_87153
  have hm1_val : my_pi (87571) = 8502 := pi_87571
  rcases le_or_gt m 417 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 87153 := bound_le_helper m 417 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 418 ≤ m := hm_gt
    have h1 : 87571 ≤ m*(m+1)/2 := bound_gt_helper m 418 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_718 (m : ℕ) (hm1 : m ≥ 1) : my_pi (718*719) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 718*719 = 516242 := by decide
  rw [hk_eq]
  have hk : my_pi (516242) = 42758 := pi_516242
  have hm0 : my_pi (86320) = 8393 := pi_86320
  have hm1_val : my_pi (86736) = 8429 := pi_86736
  rcases le_or_gt m 415 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 86320 := bound_le_helper m 415 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 416 ≤ m := hm_gt
    have h1 : 86736 ≤ m*(m+1)/2 := bound_gt_helper m 416 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_719 (m : ℕ) (hm1 : m ≥ 1) : my_pi (719*720) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 719*720 = 517680 := by decide
  rw [hk_eq]
  have hk : my_pi (517680) = 42885 := pi_517680
  have hm0 : my_pi (84666) = 8250 := pi_84666
  have hm1_val : my_pi (85078) = 8283 := pi_85078
  rcases le_or_gt m 411 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 84666 := bound_le_helper m 411 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 412 ≤ m := hm_gt
    have h1 : 85078 ≤ m*(m+1)/2 := bound_gt_helper m 412 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_720 (m : ℕ) (hm1 : m ≥ 1) : my_pi (720*721) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 720*721 = 519120 := by decide
  rw [hk_eq]
  have hk : my_pi (519120) = 42993 := pi_519120
  have hm0 : my_pi (83436) = 8145 := pi_83436
  have hm1_val : my_pi (83845) = 8178 := pi_83845
  rcases le_or_gt m 408 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 83436 := bound_le_helper m 408 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 409 ≤ m := hm_gt
    have h1 : 83845 ≤ m*(m+1)/2 := bound_gt_helper m 409 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_721 (m : ℕ) (hm1 : m ≥ 1) : my_pi (721*722) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 721*722 = 520562 := by decide
  rw [hk_eq]
  have hk : my_pi (520562) = 43101 := pi_520562
  have hm0 : my_pi (82215) = 8038 := pi_82215
  have hm1_val : my_pi (82621) = 8078 := pi_82621
  rcases le_or_gt m 405 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 82215 := bound_le_helper m 405 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 406 ≤ m := hm_gt
    have h1 : 82621 ≤ m*(m+1)/2 := bound_gt_helper m 406 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_722 (m : ℕ) (hm1 : m ≥ 1) : my_pi (722*723) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 722*723 = 522006 := by decide
  rw [hk_eq]
  have hk : my_pi (522006) = 43217 := pi_522006
  have hm0 : my_pi (81003) = 7926 := pi_81003
  have hm1_val : my_pi (81406) = 7965 := pi_81406
  rcases le_or_gt m 402 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 81003 := bound_le_helper m 402 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 403 ≤ m := hm_gt
    have h1 : 81406 ≤ m*(m+1)/2 := bound_gt_helper m 403 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_723 (m : ℕ) (hm1 : m ≥ 1) : my_pi (723*724) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 723*724 = 523452 := by decide
  rw [hk_eq]
  have hk : my_pi (523452) = 43321 := pi_523452
  have hm0 : my_pi (79800) = 7813 := pi_79800
  have hm1_val : my_pi (80200) = 7852 := pi_80200
  rcases le_or_gt m 399 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 79800 := bound_le_helper m 399 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 400 ≤ m := hm_gt
    have h1 : 80200 ≤ m*(m+1)/2 := bound_gt_helper m 400 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_724 (m : ℕ) (hm1 : m ≥ 1) : my_pi (724*725) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 724*725 = 524900 := by decide
  rw [hk_eq]
  have hk : my_pi (524900) = 43429 := pi_524900
  have hm0 : my_pi (78606) = 7713 := pi_78606
  have hm1_val : my_pi (79003) = 7746 := pi_79003
  rcases le_or_gt m 396 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 78606 := bound_le_helper m 396 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 397 ≤ m := hm_gt
    have h1 : 79003 ≤ m*(m+1)/2 := bound_gt_helper m 397 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_725 (m : ℕ) (hm1 : m ≥ 1) : my_pi (725*726) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 725*726 = 526350 := by decide
  rw [hk_eq]
  have hk : my_pi (526350) = 43548 := pi_526350
  have hm0 : my_pi (77421) = 7606 := pi_77421
  have hm1_val : my_pi (77815) = 7649 := pi_77815
  rcases le_or_gt m 393 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 77421 := bound_le_helper m 393 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 394 ≤ m := hm_gt
    have h1 : 77815 ≤ m*(m+1)/2 := bound_gt_helper m 394 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_726 (m : ℕ) (hm1 : m ≥ 1) : my_pi (726*727) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 726*727 = 527802 := by decide
  rw [hk_eq]
  have hk : my_pi (527802) = 43661 := pi_527802
  have hm0 : my_pi (75855) = 7472 := pi_75855
  have hm1_val : my_pi (76245) = 7503 := pi_76245
  rcases le_or_gt m 389 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 75855 := bound_le_helper m 389 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 390 ≤ m := hm_gt
    have h1 : 76245 ≤ m*(m+1)/2 := bound_gt_helper m 390 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_727 (m : ℕ) (hm1 : m ≥ 1) : my_pi (727*728) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 727*728 = 529256 := by decide
  rw [hk_eq]
  have hk : my_pi (529256) = 43769 := pi_529256
  have hm0 : my_pi (74691) = 7363 := pi_74691
  have hm1_val : my_pi (75078) = 7399 := pi_75078
  rcases le_or_gt m 386 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 74691 := bound_le_helper m 386 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 387 ≤ m := hm_gt
    have h1 : 75078 ≤ m*(m+1)/2 := bound_gt_helper m 387 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_728 (m : ℕ) (hm1 : m ≥ 1) : my_pi (728*729) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 728*729 = 530712 := by decide
  rw [hk_eq]
  have hk : my_pi (530712) = 43882 := pi_530712
  have hm0 : my_pi (73536) = 7260 := pi_73536
  have hm1_val : my_pi (73920) = 7295 := pi_73920
  rcases le_or_gt m 383 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 73536 := bound_le_helper m 383 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 384 ≤ m := hm_gt
    have h1 : 73920 ≤ m*(m+1)/2 := bound_gt_helper m 384 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_729 (m : ℕ) (hm1 : m ≥ 1) : my_pi (729*730) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 729*730 = 532170 := by decide
  rw [hk_eq]
  have hk : my_pi (532170) = 43985 := pi_532170
  have hm0 : my_pi (72390) = 7164 := pi_72390
  have hm1_val : my_pi (72771) = 7197 := pi_72771
  rcases le_or_gt m 380 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 72390 := bound_le_helper m 380 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 381 ≤ m := hm_gt
    have h1 : 72771 ≤ m*(m+1)/2 := bound_gt_helper m 381 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_730 (m : ℕ) (hm1 : m ≥ 1) : my_pi (730*731) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 730*731 = 533630 := by decide
  rw [hk_eq]
  have hk : my_pi (533630) = 44096 := pi_533630
  have hm0 : my_pi (71253) = 7053 := pi_71253
  have hm1_val : my_pi (71631) = 7091 := pi_71631
  rcases le_or_gt m 377 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 71253 := bound_le_helper m 377 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 378 ≤ m := hm_gt
    have h1 : 71631 ≤ m*(m+1)/2 := bound_gt_helper m 378 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_731 (m : ℕ) (hm1 : m ≥ 1) : my_pi (731*732) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 731*732 = 535092 := by decide
  rw [hk_eq]
  have hk : my_pi (535092) = 44203 := pi_535092
  have hm0 : my_pi (70125) = 6949 := pi_70125
  have hm1_val : my_pi (70500) = 6985 := pi_70500
  rcases le_or_gt m 374 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 70125 := bound_le_helper m 374 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 375 ≤ m := hm_gt
    have h1 : 70500 ≤ m*(m+1)/2 := bound_gt_helper m 375 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_732 (m : ℕ) (hm1 : m ≥ 1) : my_pi (732*733) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 732*733 = 536556 := by decide
  rw [hk_eq]
  have hk : my_pi (536556) = 44317 := pi_536556
  have hm0 : my_pi (68635) = 6822 := pi_68635
  have hm1_val : my_pi (69006) = 6855 := pi_69006
  rcases le_or_gt m 370 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 68635 := bound_le_helper m 370 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 371 ≤ m := hm_gt
    have h1 : 69006 ≤ m*(m+1)/2 := bound_gt_helper m 371 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_733 (m : ℕ) (hm1 : m ≥ 1) : my_pi (733*734) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 733*734 = 538022 := by decide
  rw [hk_eq]
  have hk : my_pi (538022) = 44425 := pi_538022
  have hm0 : my_pi (67528) = 6727 := pi_67528
  have hm1_val : my_pi (67896) = 6762 := pi_67896
  rcases le_or_gt m 367 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 67528 := bound_le_helper m 367 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 368 ≤ m := hm_gt
    have h1 : 67896 ≤ m*(m+1)/2 := bound_gt_helper m 368 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_734 (m : ℕ) (hm1 : m ≥ 1) : my_pi (734*735) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 734*735 = 539490 := by decide
  rw [hk_eq]
  have hk : my_pi (539490) = 44538 := pi_539490
  have hm0 : my_pi (66066) = 6595 := pi_66066
  have hm1_val : my_pi (66430) = 6623 := pi_66430
  rcases le_or_gt m 363 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 66066 := bound_le_helper m 363 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 364 ≤ m := hm_gt
    have h1 : 66430 ≤ m*(m+1)/2 := bound_gt_helper m 364 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_735 (m : ℕ) (hm1 : m ≥ 1) : my_pi (735*736) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 735*736 = 540960 := by decide
  rw [hk_eq]
  have hk : my_pi (540960) = 44643 := pi_540960
  have hm0 : my_pi (64980) = 6492 := pi_64980
  have hm1_val : my_pi (65341) = 6526 := pi_65341
  rcases le_or_gt m 360 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 64980 := bound_le_helper m 360 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 361 ≤ m := hm_gt
    have h1 : 65341 ≤ m*(m+1)/2 := bound_gt_helper m 361 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_736 (m : ℕ) (hm1 : m ≥ 1) : my_pi (736*737) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 736*737 = 542432 := by decide
  rw [hk_eq]
  have hk : my_pi (542432) = 44755 := pi_542432
  have hm0 : my_pi (63546) = 6369 := pi_63546
  have hm1_val : my_pi (63903) = 6407 := pi_63903
  rcases le_or_gt m 356 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 63546 := bound_le_helper m 356 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 357 ≤ m := hm_gt
    have h1 : 63903 ≤ m*(m+1)/2 := bound_gt_helper m 357 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_737 (m : ℕ) (hm1 : m ≥ 1) : my_pi (737*738) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 737*738 = 543906 := by decide
  rw [hk_eq]
  have hk : my_pi (543906) = 44876 := pi_543906
  have hm0 : my_pi (62481) = 6273 := pi_62481
  have hm1_val : my_pi (62835) = 6304 := pi_62835
  rcases le_or_gt m 353 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 62481 := bound_le_helper m 353 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 354 ≤ m := hm_gt
    have h1 : 62835 ≤ m*(m+1)/2 := bound_gt_helper m 354 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_738 (m : ℕ) (hm1 : m ≥ 1) : my_pi (738*739) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 738*739 = 545382 := by decide
  rw [hk_eq]
  have hk : my_pi (545382) = 44972 := pi_545382
  have hm0 : my_pi (61425) = 6179 := pi_61425
  have hm1_val : my_pi (61776) = 6214 := pi_61776
  rcases le_or_gt m 350 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 61425 := bound_le_helper m 350 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 351 ≤ m := hm_gt
    have h1 : 61776 ≤ m*(m+1)/2 := bound_gt_helper m 351 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_739 (m : ℕ) (hm1 : m ≥ 1) : my_pi (739*740) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 739*740 = 546860 := by decide
  rw [hk_eq]
  have hk : my_pi (546860) = 45080 := pi_546860
  have hm0 : my_pi (60031) = 6060 := pi_60031
  have hm1_val : my_pi (60378) = 6091 := pi_60378
  rcases le_or_gt m 346 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 60031 := bound_le_helper m 346 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 347 ≤ m := hm_gt
    have h1 : 60378 ≤ m*(m+1)/2 := bound_gt_helper m 347 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_740 (m : ℕ) (hm1 : m ≥ 1) : my_pi (740*741) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 740*741 = 548340 := by decide
  rw [hk_eq]
  have hk : my_pi (548340) = 45189 := pi_548340
  have hm0 : my_pi (58996) = 5962 := pi_58996
  have hm1_val : my_pi (59340) = 5996 := pi_59340
  rcases le_or_gt m 343 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 58996 := bound_le_helper m 343 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 344 ≤ m := hm_gt
    have h1 : 59340 ≤ m*(m+1)/2 := bound_gt_helper m 344 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_741 (m : ℕ) (hm1 : m ≥ 1) : my_pi (741*742) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 741*742 = 549822 := by decide
  rw [hk_eq]
  have hk : my_pi (549822) = 45311 := pi_549822
  have hm0 : my_pi (57630) = 5836 := pi_57630
  have hm1_val : my_pi (57970) = 5870 := pi_57970
  rcases le_or_gt m 339 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 57630 := bound_le_helper m 339 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 340 ≤ m := hm_gt
    have h1 : 57970 ≤ m*(m+1)/2 := bound_gt_helper m 340 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_742 (m : ℕ) (hm1 : m ≥ 1) : my_pi (742*743) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 742*743 = 551306 := by decide
  rw [hk_eq]
  have hk : my_pi (551306) = 45423 := pi_551306
  have hm0 : my_pi (56280) = 5709 := pi_56280
  have hm1_val : my_pi (56616) = 5741 := pi_56616
  rcases le_or_gt m 335 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 56280 := bound_le_helper m 335 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 336 ≤ m := hm_gt
    have h1 : 56616 ≤ m*(m+1)/2 := bound_gt_helper m 336 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_743 (m : ℕ) (hm1 : m ≥ 1) : my_pi (743*744) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 743*744 = 552792 := by decide
  rw [hk_eq]
  have hk : my_pi (552792) = 45532 := pi_552792
  have hm0 : my_pi (55278) = 5615 := pi_55278
  have hm1_val : my_pi (55611) = 5641 := pi_55611
  rcases le_or_gt m 332 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 55278 := bound_le_helper m 332 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 333 ≤ m := hm_gt
    have h1 : 55611 ≤ m*(m+1)/2 := bound_gt_helper m 333 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_744 (m : ℕ) (hm1 : m ≥ 1) : my_pi (744*745) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 744*745 = 554280 := by decide
  rw [hk_eq]
  have hk : my_pi (554280) = 45648 := pi_554280
  have hm0 : my_pi (53956) = 5497 := pi_53956
  have hm1_val : my_pi (54285) = 5521 := pi_54285
  rcases le_or_gt m 328 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 53956 := bound_le_helper m 328 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 329 ≤ m := hm_gt
    have h1 : 54285 ≤ m*(m+1)/2 := bound_gt_helper m 329 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_745 (m : ℕ) (hm1 : m ≥ 1) : my_pi (745*746) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 745*746 = 555770 := by decide
  rw [hk_eq]
  have hk : my_pi (555770) = 45755 := pi_555770
  have hm0 : my_pi (52650) = 5375 := pi_52650
  have hm1_val : my_pi (52975) = 5406 := pi_52975
  rcases le_or_gt m 324 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 52650 := bound_le_helper m 324 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 325 ≤ m := hm_gt
    have h1 : 52975 ≤ m*(m+1)/2 := bound_gt_helper m 325 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_746 (m : ℕ) (hm1 : m ≥ 1) : my_pi (746*747) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 746*747 = 557262 := by decide
  rw [hk_eq]
  have hk : my_pi (557262) = 45868 := pi_557262
  have hm0 : my_pi (51360) = 5254 := pi_51360
  have hm1_val : my_pi (51681) = 5289 := pi_51681
  rcases le_or_gt m 320 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 51360 := bound_le_helper m 320 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 321 ≤ m := hm_gt
    have h1 : 51681 ≤ m*(m+1)/2 := bound_gt_helper m 321 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_747 (m : ℕ) (hm1 : m ≥ 1) : my_pi (747*748) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 747*748 = 558756 := by decide
  rw [hk_eq]
  have hk : my_pi (558756) = 45976 := pi_558756
  have hm0 : my_pi (50403) = 5172 := pi_50403
  have hm1_val : my_pi (50721) = 5197 := pi_50721
  rcases le_or_gt m 317 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 50403 := bound_le_helper m 317 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 318 ≤ m := hm_gt
    have h1 : 50721 ≤ m*(m+1)/2 := bound_gt_helper m 318 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_748 (m : ℕ) (hm1 : m ≥ 1) : my_pi (748*749) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 748*749 = 560252 := by decide
  rw [hk_eq]
  have hk : my_pi (560252) = 46101 := pi_560252
  have hm0 : my_pi (49141) = 5051 := pi_49141
  have hm1_val : my_pi (49455) = 5081 := pi_49455
  rcases le_or_gt m 313 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 49141 := bound_le_helper m 313 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 314 ≤ m := hm_gt
    have h1 : 49455 ≤ m*(m+1)/2 := bound_gt_helper m 314 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_749 (m : ℕ) (hm1 : m ≥ 1) : my_pi (749*750) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 749*750 = 561750 := by decide
  rw [hk_eq]
  have hk : my_pi (561750) = 46202 := pi_561750
  have hm0 : my_pi (47895) = 4935 := pi_47895
  have hm1_val : my_pi (48205) = 4963 := pi_48205
  rcases le_or_gt m 309 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 47895 := bound_le_helper m 309 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 310 ≤ m := hm_gt
    have h1 : 48205 ≤ m*(m+1)/2 := bound_gt_helper m 310 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_750 (m : ℕ) (hm1 : m ≥ 1) : my_pi (750*751) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 750*751 = 563250 := by decide
  rw [hk_eq]
  have hk : my_pi (563250) = 46322 := pi_563250
  have hm0 : my_pi (46665) = 4822 := pi_46665
  have hm1_val : my_pi (46971) = 4849 := pi_46971
  rcases le_or_gt m 305 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 46665 := bound_le_helper m 305 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 306 ≤ m := hm_gt
    have h1 : 46971 ≤ m*(m+1)/2 := bound_gt_helper m 306 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_751 (m : ℕ) (hm1 : m ≥ 1) : my_pi (751*752) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 751*752 = 564752 := by decide
  rw [hk_eq]
  have hk : my_pi (564752) = 46428 := pi_564752
  have hm0 : my_pi (45451) = 4714 := pi_45451
  have hm1_val : my_pi (45753) = 4739 := pi_45753
  rcases le_or_gt m 301 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 45451 := bound_le_helper m 301 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 302 ≤ m := hm_gt
    have h1 : 45753 ≤ m*(m+1)/2 := bound_gt_helper m 302 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_752 (m : ℕ) (hm1 : m ≥ 1) : my_pi (752*753) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 752*753 = 566256 := by decide
  rw [hk_eq]
  have hk : my_pi (566256) = 46543 := pi_566256
  have hm0 : my_pi (44253) = 4604 := pi_44253
  have hm1_val : my_pi (44551) = 4632 := pi_44551
  rcases le_or_gt m 297 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 44253 := bound_le_helper m 297 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 298 ≤ m := hm_gt
    have h1 : 44551 ≤ m*(m+1)/2 := bound_gt_helper m 298 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_753 (m : ℕ) (hm1 : m ≥ 1) : my_pi (753*754) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 753*754 = 567762 := by decide
  rw [hk_eq]
  have hk : my_pi (567762) = 46647 := pi_567762
  have hm0 : my_pi (43071) = 4502 := pi_43071
  have hm1_val : my_pi (43365) = 4522 := pi_43365
  rcases le_or_gt m 293 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 43071 := bound_le_helper m 293 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 294 ≤ m := hm_gt
    have h1 : 43365 ≤ m*(m+1)/2 := bound_gt_helper m 294 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_754 (m : ℕ) (hm1 : m ≥ 1) : my_pi (754*755) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 754*755 = 569270 := by decide
  rw [hk_eq]
  have hk : my_pi (569270) = 46767 := pi_569270
  have hm0 : my_pi (41905) = 4381 := pi_41905
  have hm1_val : my_pi (42195) = 4411 := pi_42195
  rcases le_or_gt m 289 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 41905 := bound_le_helper m 289 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 290 ≤ m := hm_gt
    have h1 : 42195 ≤ m*(m+1)/2 := bound_gt_helper m 290 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_755 (m : ℕ) (hm1 : m ≥ 1) : my_pi (755*756) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 755*756 = 570780 := by decide
  rw [hk_eq]
  have hk : my_pi (570780) = 46886 := pi_570780
  have hm0 : my_pi (40755) = 4266 := pi_40755
  have hm1_val : my_pi (41041) = 4295 := pi_41041
  rcases le_or_gt m 285 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 40755 := bound_le_helper m 285 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 286 ≤ m := hm_gt
    have h1 : 41041 ≤ m*(m+1)/2 := bound_gt_helper m 286 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_756 (m : ℕ) (hm1 : m ≥ 1) : my_pi (756*757) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 756*757 = 572292 := by decide
  rw [hk_eq]
  have hk : my_pi (572292) = 46998 := pi_572292
  have hm0 : my_pi (39340) = 4140 := pi_39340
  have hm1_val : my_pi (39621) = 4166 := pi_39621
  rcases le_or_gt m 280 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 39340 := bound_le_helper m 280 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 281 ≤ m := hm_gt
    have h1 : 39621 ≤ m*(m+1)/2 := bound_gt_helper m 281 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_757 (m : ℕ) (hm1 : m ≥ 1) : my_pi (757*758) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 757*758 = 573806 := by decide
  rw [hk_eq]
  have hk : my_pi (573806) = 47116 := pi_573806
  have hm0 : my_pi (38226) = 4034 := pi_38226
  have hm1_val : my_pi (38503) = 4059 := pi_38503
  rcases le_or_gt m 276 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 38226 := bound_le_helper m 276 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 277 ≤ m := hm_gt
    have h1 : 38503 ≤ m*(m+1)/2 := bound_gt_helper m 277 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_758 (m : ℕ) (hm1 : m ≥ 1) : my_pi (758*759) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 758*759 = 575322 := by decide
  rw [hk_eq]
  have hk : my_pi (575322) = 47229 := pi_575322
  have hm0 : my_pi (36856) = 3907 := pi_36856
  have hm1_val : my_pi (37128) = 3935 := pi_37128
  rcases le_or_gt m 271 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 36856 := bound_le_helper m 271 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 272 ≤ m := hm_gt
    have h1 : 37128 ≤ m*(m+1)/2 := bound_gt_helper m 272 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_759 (m : ℕ) (hm1 : m ≥ 1) : my_pi (759*760) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 759*760 = 576840 := by decide
  rw [hk_eq]
  have hk : my_pi (576840) = 47350 := pi_576840
  have hm0 : my_pi (35778) = 3801 := pi_35778
  have hm1_val : my_pi (36046) = 3829 := pi_36046
  rcases le_or_gt m 267 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 35778 := bound_le_helper m 267 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 268 ≤ m := hm_gt
    have h1 : 36046 ≤ m*(m+1)/2 := bound_gt_helper m 268 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_760 (m : ℕ) (hm1 : m ≥ 1) : my_pi (760*761) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 760*761 = 578360 := by decide
  rw [hk_eq]
  have hk : my_pi (578360) = 47459 := pi_578360
  have hm0 : my_pi (34453) = 3679 := pi_34453
  have hm1_val : my_pi (34716) = 3707 := pi_34716
  rcases le_or_gt m 262 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 34453 := bound_le_helper m 262 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 263 ≤ m := hm_gt
    have h1 : 34716 ≤ m*(m+1)/2 := bound_gt_helper m 263 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_761 (m : ℕ) (hm1 : m ≥ 1) : my_pi (761*762) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 761*762 = 579882 := by decide
  rw [hk_eq]
  have hk : my_pi (579882) = 47579 := pi_579882
  have hm0 : my_pi (33153) = 3553 := pi_33153
  have hm1_val : my_pi (33411) = 3578 := pi_33411
  rcases le_or_gt m 257 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 33153 := bound_le_helper m 257 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 258 ≤ m := hm_gt
    have h1 : 33411 ≤ m*(m+1)/2 := bound_gt_helper m 258 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_762 (m : ℕ) (hm1 : m ≥ 1) : my_pi (762*763) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 762*763 = 581406 := by decide
  rw [hk_eq]
  have hk : my_pi (581406) = 47694 := pi_581406
  have hm0 : my_pi (32131) = 3447 := pi_32131
  have hm1_val : my_pi (32385) = 3476 := pi_32385
  rcases le_or_gt m 253 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 32131 := bound_le_helper m 253 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 254 ≤ m := hm_gt
    have h1 : 32385 ≤ m*(m+1)/2 := bound_gt_helper m 254 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_763 (m : ℕ) (hm1 : m ≥ 1) : my_pi (763*764) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 763*764 = 582932 := by decide
  rw [hk_eq]
  have hk : my_pi (582932) = 47807 := pi_582932
  have hm0 : my_pi (30876) = 3330 := pi_30876
  have hm1_val : my_pi (31125) = 3352 := pi_31125
  rcases le_or_gt m 248 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 30876 := bound_le_helper m 248 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 249 ≤ m := hm_gt
    have h1 : 31125 ≤ m*(m+1)/2 := bound_gt_helper m 249 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_764 (m : ℕ) (hm1 : m ≥ 1) : my_pi (764*765) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 764*765 = 584460 := by decide
  rw [hk_eq]
  have hk : my_pi (584460) = 47920 := pi_584460
  have hm0 : my_pi (29646) = 3217 := pi_29646
  have hm1_val : my_pi (29890) = 3238 := pi_29890
  rcases le_or_gt m 243 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 29646 := bound_le_helper m 243 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 244 ≤ m := hm_gt
    have h1 : 29890 ≤ m*(m+1)/2 := bound_gt_helper m 244 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_765 (m : ℕ) (hm1 : m ≥ 1) : my_pi (765*766) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 765*766 = 585990 := by decide
  rw [hk_eq]
  have hk : my_pi (585990) = 48043 := pi_585990
  have hm0 : my_pi (28441) = 3095 := pi_28441
  have hm1_val : my_pi (28680) = 3124 := pi_28680
  rcases le_or_gt m 238 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 28441 := bound_le_helper m 238 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 239 ≤ m := hm_gt
    have h1 : 28680 ≤ m*(m+1)/2 := bound_gt_helper m 239 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_766 (m : ℕ) (hm1 : m ≥ 1) : my_pi (766*767) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 766*767 = 587522 := by decide
  rw [hk_eq]
  have hk : my_pi (587522) = 48166 := pi_587522
  have hm0 : my_pi (27261) = 2984 := pi_27261
  have hm1_val : my_pi (27495) = 3004 := pi_27495
  rcases le_or_gt m 233 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 27261 := bound_le_helper m 233 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 234 ≤ m := hm_gt
    have h1 : 27495 ≤ m*(m+1)/2 := bound_gt_helper m 234 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_767 (m : ℕ) (hm1 : m ≥ 1) : my_pi (767*768) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 767*768 = 589056 := by decide
  rw [hk_eq]
  have hk : my_pi (589056) = 48286 := pi_589056
  have hm0 : my_pi (26106) = 2868 := pi_26106
  have hm1_val : my_pi (26335) = 2893 := pi_26335
  rcases le_or_gt m 228 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 26106 := bound_le_helper m 228 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 229 ≤ m := hm_gt
    have h1 : 26335 ≤ m*(m+1)/2 := bound_gt_helper m 229 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_768 (m : ℕ) (hm1 : m ≥ 1) : my_pi (768*769) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 768*769 = 590592 := by decide
  rw [hk_eq]
  have hk : my_pi (590592) = 48392 := pi_590592
  have hm0 : my_pi (24976) = 2759 := pi_24976
  have hm1_val : my_pi (25200) = 2781 := pi_25200
  rcases le_or_gt m 223 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 24976 := bound_le_helper m 223 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 224 ≤ m := hm_gt
    have h1 : 25200 ≤ m*(m+1)/2 := bound_gt_helper m 224 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_769 (m : ℕ) (hm1 : m ≥ 1) : my_pi (769*770) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 769*770 = 592130 := by decide
  rw [hk_eq]
  have hk : my_pi (592130) = 48499 := pi_592130
  have hm0 : my_pi (23871) = 2654 := pi_23871
  have hm1_val : my_pi (24090) = 2679 := pi_24090
  rcases le_or_gt m 218 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 23871 := bound_le_helper m 218 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 219 ≤ m := hm_gt
    have h1 : 24090 ≤ m*(m+1)/2 := bound_gt_helper m 219 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_770 (m : ℕ) (hm1 : m ≥ 1) : my_pi (770*771) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 770*771 = 593670 := by decide
  rw [hk_eq]
  have hk : my_pi (593670) = 48628 := pi_593670
  have hm0 : my_pi (22578) = 2524 := pi_22578
  have hm1_val : my_pi (22791) = 2547 := pi_22791
  rcases le_or_gt m 212 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 22578 := bound_le_helper m 212 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 213 ≤ m := hm_gt
    have h1 : 22791 ≤ m*(m+1)/2 := bound_gt_helper m 213 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_771 (m : ℕ) (hm1 : m ≥ 1) : my_pi (771*772) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 771*772 = 595212 := by decide
  rw [hk_eq]
  have hk : my_pi (595212) = 48746 := pi_595212
  have hm0 : my_pi (21321) = 2394 := pi_21321
  have hm1_val : my_pi (21528) = 2416 := pi_21528
  rcases le_or_gt m 206 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 21321 := bound_le_helper m 206 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 207 ≤ m := hm_gt
    have h1 : 21528 ≤ m*(m+1)/2 := bound_gt_helper m 207 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_772 (m : ℕ) (hm1 : m ≥ 1) : my_pi (772*773) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 772*773 = 596756 := by decide
  rw [hk_eq]
  have hk : my_pi (596756) = 48858 := pi_596756
  have hm0 : my_pi (20301) = 2293 := pi_20301
  have hm1_val : my_pi (20503) = 2313 := pi_20503
  rcases le_or_gt m 201 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 20301 := bound_le_helper m 201 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 202 ≤ m := hm_gt
    have h1 : 20503 ≤ m*(m+1)/2 := bound_gt_helper m 202 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_773 (m : ℕ) (hm1 : m ≥ 1) : my_pi (773*774) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 773*774 = 598302 := by decide
  rw [hk_eq]
  have hk : my_pi (598302) = 48972 := pi_598302
  have hm0 : my_pi (19110) = 2169 := pi_19110
  have hm1_val : my_pi (19306) = 2188 := pi_19306
  rcases le_or_gt m 195 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 19110 := bound_le_helper m 195 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 196 ≤ m := hm_gt
    have h1 : 19306 ≤ m*(m+1)/2 := bound_gt_helper m 196 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_774 (m : ℕ) (hm1 : m ≥ 1) : my_pi (774*775) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 774*775 = 599850 := by decide
  rw [hk_eq]
  have hk : my_pi (599850) = 49086 := pi_599850
  have hm0 : my_pi (17955) = 2057 := pi_17955
  have hm1_val : my_pi (18145) = 2080 := pi_18145
  rcases le_or_gt m 189 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 17955 := bound_le_helper m 189 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 190 ≤ m := hm_gt
    have h1 : 18145 ≤ m*(m+1)/2 := bound_gt_helper m 190 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_775 (m : ℕ) (hm1 : m ≥ 1) : my_pi (775*776) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 775*776 = 601400 := by decide
  rw [hk_eq]
  have hk : my_pi (601400) = 49207 := pi_601400
  have hm0 : my_pi (16836) = 1943 := pi_16836
  have hm1_val : my_pi (17020) = 1961 := pi_17020
  rcases le_or_gt m 183 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 16836 := bound_le_helper m 183 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 184 ≤ m := hm_gt
    have h1 : 17020 ≤ m*(m+1)/2 := bound_gt_helper m 184 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_776 (m : ℕ) (hm1 : m ≥ 1) : my_pi (776*777) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 776*777 = 602952 := by decide
  rw [hk_eq]
  have hk : my_pi (602952) = 49326 := pi_602952
  have hm0 : my_pi (15576) = 1816 := pi_15576
  have hm1_val : my_pi (15753) = 1837 := pi_15753
  rcases le_or_gt m 176 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 15576 := bound_le_helper m 176 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 177 ≤ m := hm_gt
    have h1 : 15753 ≤ m*(m+1)/2 := bound_gt_helper m 177 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_777 (m : ℕ) (hm1 : m ≥ 1) : my_pi (777*778) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 777*778 = 604506 := by decide
  rw [hk_eq]
  have hk : my_pi (604506) = 49439 := pi_604506
  have hm0 : my_pi (14535) = 1701 := pi_14535
  have hm1_val : my_pi (14706) = 1720 := pi_14706
  rcases le_or_gt m 170 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 14535 := bound_le_helper m 170 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 171 ≤ m := hm_gt
    have h1 : 14706 ≤ m*(m+1)/2 := bound_gt_helper m 171 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_778 (m : ℕ) (hm1 : m ≥ 1) : my_pi (778*779) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 778*779 = 606062 := by decide
  rw [hk_eq]
  have hk : my_pi (606062) = 49560 := pi_606062
  have hm0 : my_pi (13366) = 1585 := pi_13366
  have hm1_val : my_pi (13530) = 1602 := pi_13530
  rcases le_or_gt m 163 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 13366 := bound_le_helper m 163 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 164 ≤ m := hm_gt
    have h1 : 13530 ≤ m*(m+1)/2 := bound_gt_helper m 164 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_779 (m : ℕ) (hm1 : m ≥ 1) : my_pi (779*780) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 779*780 = 607620 := by decide
  rw [hk_eq]
  have hk : my_pi (607620) = 49674 := pi_607620
  have hm0 : my_pi (12403) = 1480 := pi_12403
  have hm1_val : my_pi (12561) = 1500 := pi_12561
  rcases le_or_gt m 157 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 12403 := bound_le_helper m 157 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 158 ≤ m := hm_gt
    have h1 : 12561 ≤ m*(m+1)/2 := bound_gt_helper m 158 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_780 (m : ℕ) (hm1 : m ≥ 1) : my_pi (780*781) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 780*781 = 609180 := by decide
  rw [hk_eq]
  have hk : my_pi (609180) = 49794 := pi_609180
  have hm0 : my_pi (11175) = 1354 := pi_11175
  have hm1_val : my_pi (11325) = 1369 := pi_11325
  rcases le_or_gt m 149 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 11175 := bound_le_helper m 149 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 150 ≤ m := hm_gt
    have h1 : 11325 ≤ m*(m+1)/2 := bound_gt_helper m 150 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_781 (m : ℕ) (hm1 : m ≥ 1) : my_pi (781*782) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 781*782 = 610742 := by decide
  rw [hk_eq]
  have hk : my_pi (610742) = 49911 := pi_610742
  have hm0 : my_pi (10011) = 1231 := pi_10011
  have hm1_val : my_pi (10153) = 1246 := pi_10153
  rcases le_or_gt m 141 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 10011 := bound_le_helper m 141 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 142 ≤ m := hm_gt
    have h1 : 10153 ≤ m*(m+1)/2 := bound_gt_helper m 142 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_782 (m : ℕ) (hm1 : m ≥ 1) : my_pi (782*783) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 782*783 = 612306 := by decide
  rw [hk_eq]
  have hk : my_pi (612306) = 50031 := pi_612306
  have hm0 : my_pi (9045) = 1124 := pi_9045
  have hm1_val : my_pi (9180) = 1137 := pi_9180
  rcases le_or_gt m 134 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 9045 := bound_le_helper m 134 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 135 ≤ m := hm_gt
    have h1 : 9180 ≤ m*(m+1)/2 := bound_gt_helper m 135 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_783 (m : ℕ) (hm1 : m ≥ 1) : my_pi (783*784) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 783*784 = 613872 := by decide
  rw [hk_eq]
  have hk : my_pi (613872) = 50151 := pi_613872
  have hm0 : my_pi (7875) = 994 := pi_7875
  have hm1_val : my_pi (8001) = 1007 := pi_8001
  rcases le_or_gt m 125 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 7875 := bound_le_helper m 125 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 126 ≤ m := hm_gt
    have h1 : 8001 ≤ m*(m+1)/2 := bound_gt_helper m 126 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_784 (m : ℕ) (hm1 : m ≥ 1) : my_pi (784*785) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 784*785 = 615440 := by decide
  rw [hk_eq]
  have hk : my_pi (615440) = 50263 := pi_615440
  have hm0 : my_pi (6903) = 887 := pi_6903
  have hm1_val : my_pi (7021) = 903 := pi_7021
  rcases le_or_gt m 117 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 6903 := bound_le_helper m 117 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 118 ≤ m := hm_gt
    have h1 : 7021 ≤ m*(m+1)/2 := bound_gt_helper m 118 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_785 (m : ℕ) (hm1 : m ≥ 1) : my_pi (785*786) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 785*786 = 617010 := by decide
  rw [hk_eq]
  have hk : my_pi (617010) = 50391 := pi_617010
  have hm0 : my_pi (5778) = 757 := pi_5778
  have hm1_val : my_pi (5886) = 775 := pi_5886
  rcases le_or_gt m 107 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 5778 := bound_le_helper m 107 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 108 ≤ m := hm_gt
    have h1 : 5886 ≤ m*(m+1)/2 := bound_gt_helper m 108 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_786 (m : ℕ) (hm1 : m ≥ 1) : my_pi (786*787) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 786*787 = 618582 := by decide
  rw [hk_eq]
  have hk : my_pi (618582) = 50512 := pi_618582
  have hm0 : my_pi (4753) = 640 := pi_4753
  have hm1_val : my_pi (4851) = 650 := pi_4851
  rcases le_or_gt m 97 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 4753 := bound_le_helper m 97 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 98 ≤ m := hm_gt
    have h1 : 4851 ≤ m*(m+1)/2 := bound_gt_helper m 98 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_787 (m : ℕ) (hm1 : m ≥ 1) : my_pi (787*788) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 787*788 = 620156 := by decide
  rw [hk_eq]
  have hk : my_pi (620156) = 50619 := pi_620156
  have hm0 : my_pi (3828) = 531 := pi_3828
  have hm1_val : my_pi (3916) = 541 := pi_3916
  rcases le_or_gt m 87 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 3828 := bound_le_helper m 87 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 88 ≤ m := hm_gt
    have h1 : 3916 ≤ m*(m+1)/2 := bound_gt_helper m 88 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_788 (m : ℕ) (hm1 : m ≥ 1) : my_pi (788*789) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 788*789 = 621732 := by decide
  rw [hk_eq]
  have hk : my_pi (621732) = 50741 := pi_621732
  have hm0 : my_pi (2850) = 413 := pi_2850
  have hm1_val : my_pi (2926) = 422 := pi_2926
  rcases le_or_gt m 75 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 2850 := bound_le_helper m 75 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 76 ≤ m := hm_gt
    have h1 : 2926 ≤ m*(m+1)/2 := bound_gt_helper m 76 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_789 (m : ℕ) (hm1 : m ≥ 1) : my_pi (789*790) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 789*790 = 623310 := by decide
  rw [hk_eq]
  have hk : my_pi (623310) = 50853 := pi_623310
  have hm0 : my_pi (1953) = 297 := pi_1953
  have hm1_val : my_pi (2016) = 305 := pi_2016
  rcases le_or_gt m 62 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 1953 := bound_le_helper m 62 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 63 ≤ m := hm_gt
    have h1 : 2016 ≤ m*(m+1)/2 := bound_gt_helper m 63 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_790 (m : ℕ) (hm1 : m ≥ 1) : my_pi (790*791) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 790*791 = 624890 := by decide
  rw [hk_eq]
  have hk : my_pi (624890) = 50980 := pi_624890
  have hm0 : my_pi (1035) = 174 := pi_1035
  have hm1_val : my_pi (1081) = 180 := pi_1081
  rcases le_or_gt m 45 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 1035 := bound_le_helper m 45 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 46 ≤ m := hm_gt
    have h1 : 1081 ≤ m*(m+1)/2 := bound_gt_helper m 46 hm_ge
    have h2 := my_pi_mono h1
    omega

lemma no_sol_k_791 (m : ℕ) (hm1 : m ≥ 1) : my_pi (791*792) + my_pi (m*(m+1)/2) ≠ 51156 := by
  have hk_eq : 791*792 = 626472 := by decide
  rw [hk_eq]
  have hk : my_pi (626472) = 51083 := pi_626472
  have hm0 : my_pi (351) = 70 := pi_351
  have hm1_val : my_pi (378) = 74 := pi_378
  rcases le_or_gt m 26 with hm_le | hm_gt
  · have h1 : m*(m+1)/2 ≤ 351 := bound_le_helper m 26 hm_le
    have h2 := my_pi_mono h1
    omega
  · have hm_ge : 27 ≤ m := hm_gt
    have h1 : 378 ≤ m*(m+1)/2 := bound_gt_helper m 27 hm_ge
    have h2 := my_pi_mono h1
    omega

