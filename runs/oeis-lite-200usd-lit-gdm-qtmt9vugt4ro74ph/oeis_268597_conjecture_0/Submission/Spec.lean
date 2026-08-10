import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 100000
set_option maxHeartbeats 0


open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ :=
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

lemma totient_prime_power_solution (p : ℕ) (hp : p.Prime) (b : ℕ) :
  (p^(b + 1) - 1) % (p^b * (p - 1)) = p^b - 1 := by
  have hp_gt : p ≥ 2 := hp.two_le
  have h1 : p^(b + 1) - 1 = p^b * (p - 1) + (p^b - 1) := by
    rw [pow_succ]
    have hp1 : 1 ≤ p := by omega
    rw [Nat.mul_sub_left_distrib]
    rw [mul_one]
    generalize hX : p^b * p = X
    generalize hY : p^b = Y
    have h_le : Y ≤ X := by
      rw [← hX, ← hY]
      have h_le_p : 1 ≤ p := by omega
      have h6 := Nat.mul_le_mul_left (p^b) h_le_p
      rw [mul_one] at h6
      exact h6
    have hY_pos : 1 ≤ Y := by
      rw [← hY]
      exact Nat.one_le_pow b p hp.pos
    omega
  rw [h1]
  have h5 : p^b - 1 < p^b * (p - 1) := by
    have hp1 : 1 ≤ p - 1 := by omega
    have h6 : p^b * 1 ≤ p^b * (p - 1) := Nat.mul_le_mul_left (p^b) hp1
    rw [mul_one] at h6
    have hY_pos : 1 ≤ p^b := Nat.one_le_pow b p hp.pos
    omega
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5

lemma totient_two_prime_power_solution (a b : ℕ) (ha : a ≥ 1) (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
  (2^a * p^(b + 1) - 1) % (2^(a - 1) * p^b * (p - 1)) = 2^a * p^b - 1 := by
  have hp_gt : p ≥ 3 := by
    have := hp.two_le
    omega
  have h_two_pow : 2^a = 2^(a - 1) * 2 := by
    have : a = (a - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : 2^a * p^(b + 1) - 1 = 2 * (2^(a - 1) * p^b * (p - 1)) + (2^a * p^b - 1) := by
    rw [h_two_pow]
    rw [pow_succ]
    generalize hA : 2^(a - 1) = A
    generalize hB : p^b = B
    -- Now the goal is: A * 2 * (B * p) - 1 = 2 * (A * B * (p - 1)) + (A * 2 * B - 1)
    have hp_eq : p = (p - 1) + 1 := by omega
    nth_rw 1 [hp_eq]
    rw [mul_add, mul_one]
    generalize hB_p : B * (p - 1) = B_p
    have h_expand : A * 2 * (B_p + B) = A * 2 * B_p + A * 2 * B := by ring
    rw [h_expand]
    have h_assoc1 : A * 2 * B_p = 2 * (A * B_p) := by ring
    rw [h_assoc1]
    have h_assoc3 : 2 * (A * B_p) = 2 * (A * B * (p - 1)) := by
      rw [← hB_p]
      ring
    rw [h_assoc3]
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    generalize hX : 2 * (A * B * (p - 1)) = X
    generalize hY : A * 2 * B = Y
    have hY_pos : 0 < Y := by
      rw [← hY]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      exact mul_pos (mul_pos hA_pos_pos (by omega)) hB_pos_pos
    omega
  rw [h1]
  have h5 : 2^a * p^b - 1 < 2^(a - 1) * p^b * (p - 1) := by
    rw [h_two_pow]
    generalize hA : 2^(a - 1) = A
    generalize hB : p^b = B
    have hp1 : 2 ≤ p - 1 := by omega
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    have h6 : A * B * 2 ≤ A * B * (p - 1) := Nat.mul_le_mul_left (A * B) hp1
    have h7 : A * B * 2 = A * 2 * B := by ring
    rw [h7] at h6
    generalize hX : A * 2 * B = X
    generalize hY : A * B * (p - 1) = Y
    have hX_pos : 0 < X := by
      rw [← hX]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      exact mul_pos (mul_pos hA_pos_pos (by omega)) hB_pos_pos
    omega
  have h_mod_prep : 2 * (2^(a - 1) * p^b * (p - 1)) + (2^a * p^b - 1) =
    (2^(a - 1) * p^b * (p - 1)) + ((2^(a - 1) * p^b * (p - 1)) + (2^a * p^b - 1)) := by omega
  rw [h_mod_prep]
  rw [Nat.add_mod_left, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5






lemma totient_three_prime_power_solution (a b c : ℕ) (hb : b ≥ 1) (p : ℕ) (hp : p.Prime) (hp_gt : p ≥ 5) :
  (2^a * 3^b * p^(c + 1) - 1) % (2^a * 3^(b - 1) * p^c * (p - 1)) = 2^a * 3^b * p^c - 1 := by
  have h_three_pow : 3^b = 3^(b - 1) * 3 := by
    have : b = (b - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : 2^a * 3^b * p^(c + 1) - 1 = 3 * (2^a * 3^(b - 1) * p^c * (p - 1)) + (2^a * 3^b * p^c - 1) := by
    rw [h_three_pow]
    rw [pow_succ]
    generalize hA : 2^a = A
    generalize hB : 3^(b - 1) = B
    generalize hC : p^c = C
    have hp_eq : p = (p - 1) + 1 := by omega
    nth_rw 1 [hp_eq]
    rw [mul_add, mul_one]
    generalize hC_p : C * (p - 1) = C_p
    have h_expand : A * (B * 3) * (C_p + C) = A * B * 3 * C_p + A * B * 3 * C := by ring
    rw [h_expand]
    have h_assoc1 : A * B * 3 * C_p = 3 * (A * B * C_p) := by ring
    rw [h_assoc1]
    have h_assoc3 : 3 * (A * B * C_p) = 3 * (A * B * C * (p - 1)) := by
      rw [← hC_p]
      ring
    rw [h_assoc3]
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ 3 (by omega)
    have hC_pos : 1 ≤ C := by
      rw [← hC]
      exact Nat.one_le_pow _ p hp.pos
    generalize hX : 3 * (A * B * C * (p - 1)) = X
    have h_assoc_Y : A * (B * 3) * C = A * B * 3 * C := by ring
    rw [h_assoc_Y]
    generalize hY : A * B * 3 * C = Y
    have hY_pos : 0 < Y := by
      rw [← hY]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      have hC_pos_pos : 0 < C := by omega
      exact mul_pos (mul_pos (mul_pos hA_pos_pos hB_pos_pos) (by omega)) hC_pos_pos
    omega
  rw [h1]
  have h5 : 2^a * 3^b * p^c - 1 < 2^a * 3^(b - 1) * p^c * (p - 1) := by
    rw [h_three_pow]
    generalize hA : 2^a = A
    generalize hB : 3^(b - 1) = B
    generalize hC : p^c = C
    have hp1 : 4 ≤ p - 1 := by omega
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ 2 (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ 3 (by omega)
    have hC_pos : 1 ≤ C := by
      rw [← hC]
      exact Nat.one_le_pow _ p hp.pos
    have h6 : A * B * C * 3 ≤ A * B * C * (p - 1) := Nat.mul_le_mul_left (A * B * C) (by omega)
    have h7 : A * B * C * 3 = A * (B * 3) * C := by ring
    rw [h7] at h6
    generalize hX : A * (B * 3) * C = X
    generalize hY : A * B * C * (p - 1) = Y
    have hX_pos : 0 < X := by
      rw [← hX]
      have hA_pos_pos : 0 < A := by omega
      have hB_pos_pos : 0 < B := by omega
      have hC_pos_pos : 0 < C := by omega
      exact mul_pos (mul_pos hA_pos_pos (mul_pos hB_pos_pos (by omega))) hC_pos_pos
    omega
  have h_mod_prep : 3 * (2^a * 3^(b - 1) * p^c * (p - 1)) + (2^a * 3^b * p^c - 1) =
    (2^a * 3^(b - 1) * p^c * (p - 1)) + ((2^a * 3^(b - 1) * p^c * (p - 1)) + ((2^a * 3^(b - 1) * p^c * (p - 1)) + (2^a * 3^b * p^c - 1))) := by omega
  rw [h_mod_prep]
  rw [Nat.add_mod_left, Nat.add_mod_left, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5


lemma totient_general_two_odd_prime_power_solution (q a b : ℕ) (ha : a ≥ 1) (hq_gt : q ≥ 3) (p : ℕ) (hp : p.Prime) (hp_gt : p ≥ q + 2) :
  (q^a * p^(b + 1) - 1) % (q^(a - 1) * (q - 1) * p^b * (p - 1)) = q^(a - 1) * p^b * (p + q - 1) - 1 := by
  have hp_gt2 : p ≥ q + 2 := hp_gt
  have h_q_pow : q^a = q^(a - 1) * q := by
    have : a = (a - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : q^a * p^(b + 1) - 1 = (q^(a - 1) * (q - 1) * p^b * (p - 1)) + (q^(a - 1) * p^b * (p + q - 1) - 1) := by
    rw [h_q_pow]
    rw [pow_succ]
    generalize hA : q^(a - 1) = A
    generalize hB : p^b = B
    have hq_eq : q = (q - 1) + 1 := by omega
    have hp_eq : p = (p - 1) + 1 := by omega
    generalize h_q1 : q - 1 = q1
    generalize h_p1 : p - 1 = p1
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ q (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    have h_ring : A * (q1 + 1) * (B * (p1 + 1)) = A * q1 * B * p1 + A * B * (p1 + q1 + 1) := by ring
    have h_pos : 1 ≤ A * B * (p1 + q1 + 1) := by
      have : 0 < A * B * (p1 + q1 + 1) := mul_pos (mul_pos hA_pos hB_pos) (by omega)
      omega
    rw [hq_eq, hp_eq, h_q1, h_p1]
    have h_temp : p1 + 1 + (q1 + 1) - 1 = p1 + q1 + 1 := by omega
    rw [h_temp]
    rw [h_ring]
    rw [Nat.add_sub_assoc h_pos]
  rw [h1]
  have h5 : q^(a - 1) * p^b * (p + q - 1) - 1 < q^(a - 1) * (q - 1) * p^b * (p - 1) := by
    generalize hA : q^(a - 1) = A
    generalize hB : p^b = B
    have hA_pos : 1 ≤ A := by
      rw [← hA]
      exact Nat.one_le_pow _ q (by omega)
    have hB_pos : 1 ≤ B := by
      rw [← hB]
      exact Nat.one_le_pow _ p hp.pos
    have hq_ge : 3 ≤ q := hq_gt
    have hp_ge : 5 ≤ p := by omega
    generalize h_q1 : q - 1 = q1
    generalize h_p1 : p - 1 = p1
    have hq1_ge : 2 ≤ q1 := by omega
    have hp1_ge : 4 ≤ p1 := by omega
    have h_ineq : p1 + q1 + 1 < q1 * p1 := by nlinarith
    have h_left : A * B * (p + q - 1) = (A * B) * (p1 + q1 + 1) := by
      have : p + q - 1 = p1 + q1 + 1 := by omega
      rw [this]
    have h_right : A * q1 * B * p1 = (A * B) * (q1 * p1) := by ring
    rw [h_left, h_right]
    have h_diff_pos : 0 < q1 * p1 - (p1 + q1 + 1) := by omega
    have h_mul_diff_pos : 0 < (A * B) * (q1 * p1 - (p1 + q1 + 1)) := mul_pos (mul_pos hA_pos hB_pos) h_diff_pos
    have h_expand : (A * B) * (q1 * p1 - (p1 + q1 + 1)) = A * B * (q1 * p1) - A * B * (p1 + q1 + 1) := by
      rw [Nat.mul_sub_left_distrib]
    rw [h_expand] at h_mul_diff_pos
    omega
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5


lemma totient_goldbach_solution (d p : ℕ) (_hd : d.Prime) (_hp : p.Prime) (h_diff : d ≠ p) (hd_gt : d ≥ 3) (hp_gt : p ≥ 3) :
  (d * p - 1) % ((d - 1) * (p - 1)) = d + p - 2 := by
  generalize hd_sub : d - 1 = d'
  generalize hp_sub : p - 1 = p'
  have hd_eq : d = d' + 1 := by omega
  have hp_eq : p = p' + 1 := by omega
  have hd'_gt : d' ≥ 2 := by omega
  have hp'_gt : p' ≥ 2 := by omega
  have h_diff' : d' ≠ p' := by omega
  have h1 : d * p - 1 = d' * p' + (d' + p') := by
    rw [hd_eq, hp_eq]
    have h_expand : (d' + 1) * (p' + 1) = d' * p' + d' + p' + 1 := by ring
    rw [h_expand]
    omega
  have h2 : d + p - 2 = d' + p' := by omega
  rw [h1, h2]
  have h5 : d' + p' < d' * p' := by
    rcases lt_or_gt_of_ne h_diff' with h_lt | h_gt
    · -- d' < p'
      have h_mul : 2 * p' ≤ d' * p' := Nat.mul_le_mul_right p' hd'_gt
      omega
    · -- p' < d'
      have h_mul : 2 * d' ≤ p' * d' := Nat.mul_le_mul_right d' hp'_gt
      rw [mul_comm p' d'] at h_mul
      omega
  rw [Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h5


lemma totient_two_goldbach_general_solution (a : ℕ) (ha : a ≥ 1) (q p : ℕ) (hq : q.Prime) (hp : p.Prime) (hq_odd : q ≠ 2) (hp_odd : p ≠ 2) (h_diff : q ≠ p) (h_lt : 2^a * (q + p - 1) - 1 < 2^(a - 1) * (q - 1) * (p - 1)) :
  (2^a * q * p - 1) % (2^(a - 1) * (q - 1) * (p - 1)) = 2^a * (q + p - 1) - 1 := by
  have hq_ge : q ≥ 3 := by
    have := hq.two_le
    omega
  have hp_ge : p ≥ 3 := by
    have := hp.two_le
    omega
  have hq_eq : q = (q - 1) + 1 := by omega
  have hp_eq : p = (p - 1) + 1 := by omega
  have h_two_pow : 2^a = 2^(a - 1) * 2 := by
    have : a = (a - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [pow_succ]
  have h1 : 2^a * q * p - 1 = 2 * (2^(a - 1) * (q - 1) * (p - 1)) + (2^a * (q + p - 1) - 1) := by
    rw [h_two_pow]
    generalize hA : 2^(a - 1) = A
    generalize h_q1 : q - 1 = q1
    generalize h_p1 : p - 1 = p1
    have h_ring : A * 2 * (q1 + 1) * (p1 + 1) = 2 * (A * q1 * p1) + A * 2 * (q1 + p1 + 1) := by ring
    have h_pos : 1 ≤ A * 2 * (q1 + p1 + 1) := by
      have hA_pos : 1 ≤ A := by
        rw [← hA]
        exact Nat.one_le_pow _ 2 (by omega)
      have : 0 < A * 2 * (q1 + p1 + 1) := mul_pos (mul_pos hA_pos (by omega)) (by omega)
      omega
    rw [hq_eq, hp_eq, h_q1, h_p1]
    have h_temp : q1 + 1 + (p1 + 1) - 1 = q1 + p1 + 1 := by omega
    rw [h_temp]
    rw [h_ring]
    rw [Nat.add_sub_assoc h_pos]
  rw [h1]
  have h_mod_prep : 2 * (2^(a - 1) * (q - 1) * (p - 1)) + (2^a * (q + p - 1) - 1) =
    (2^(a - 1) * (q - 1) * (p - 1)) + ((2^(a - 1) * (q - 1) * (p - 1)) + (2^a * (q + p - 1) - 1)) := by omega
  rw [h_mod_prep]
  rw [Nat.add_mod_left, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt h_lt

lemma sInf_pos_of_nonempty {S : Set ℕ} (h_nonempty : S.Nonempty) (h_pos : ∀ x ∈ S, x > 0) : sInf S > 0 := by
  have h_mem : sInf S ∈ S := Nat.sInf_mem h_nonempty
  exact h_pos (sInf S) h_mem



def witness (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 4
  | 2 => 9
  | 3 => 8
  | 4 => 25
  | 5 => 18
  | 6 => 15
  | 7 => 16
  | 8 => 21
  | 9 => 50
  | 10 => 35
  | 11 => 36
  | 12 => 33
  | 13 => 98
  | 14 => 39
  | 15 => 32
  | 16 => 65
  | 17 => 54
  | 18 => 51
  | 19 => 100
  | 20 => 45
  | 21 => 70
  | 22 => 95
  | 23 => 72
  | 24 => 69
  | 25 => 338
  | 26 => 63
  | 27 => 196
  | 28 => 161
  | 29 => 110
  | 30 => 87
  | 31 => 64
  | 32 => 93
  | 33 => 130
  | 34 => 75
  | 35 => 108
  | 36 => 217
  | 37 => 182
  | 38 => 99
  | 39 => 200
  | 40 => 185
  | 41 => 170
  | 42 => 123
  | 43 => 140
  | 44 => 117
  | 45 => 190
  | 46 => 215
  | 47 => 144
  | 48 => 141
  | 49 => 250
  | 50 => 235
  | 51 => 676
  | 52 => 329
  | 53 => 162
  | 54 => 159
  | 55 => 392
  | 56 => 153
  | 57 => 322
  | 58 => 371
  | 59 => 220
  | 60 => 177
  | 61 => 494
  | 62 => 135
  | 63 => 128
  | 64 => 305
  | 65 => 290
  | 66 => 427
  | 67 => 260
  | 68 => 201
  | 69 => 310
  | 70 => 335
  | 71 => 216
  | 72 => 213
  | 73 => 434
  | 74 => 207
  | 75 => 364
  | 76 => 245
  | 77 => 638
  | 78 => 511
  | 79 => 400
  | 80 => 189
  | 81 => 370
  | 82 => 395
  | 83 => 340
  | 84 => 249
  | 85 => 518
  | 86 => 415
  | 87 => 280
  | 88 => 581
  | 89 => 410
  | 90 => 267
  | 91 => 380
  | 92 => 261
  | 93 => 430
  | 94 => 623
  | 95 => 288
  | 96 => 1501
  | 97 => 602
  | 98 => 279
  | 99 => 500
  | 100 => 485
  | 101 => 462
  | 102 => 303
  | 103 => 1352
  | 104 => 225
  | 105 => 658
  | 106 => 515
  | 107 => 324
  | 108 => 321
  | 109 => 350
  | 110 => 231
  | 111 => 784
  | 112 => 545
  | 113 => 530
  | 114 => 339
  | 115 => 644
  | 116 => 297
  | 117 => 742
  | 118 => 539
  | 119 => 440
  | 120 => 1331
  | 121 => 1634
  | 122 => 1243
  | 123 => 988
  | 124 => 625
  | 125 => 510
  | 126 => 255
  | 127 => 256
  | 128 => 273
  | 129 => 610
  | 130 => 635
  | 131 => 580
  | 132 => 393
  | 133 => 854
  | 134 => 351
  | 135 => 520
  | 136 => 917
  | 137 => 570
  | 138 => 411
  | 139 => 620
  | 140 => 285
  | 141 => 670
  | 142 => 363
  | 143 => 432
  | 144 => 385
  | 145 => 938
  | 146 => 423
  | 147 => 868
  | 148 => 1529
  | 149 => 550
  | 150 => 447
  | 151 => 728
  | 152 => 453
  | 153 => 490
  | 154 => 755
  | 155 => 1276
  | 156 => 1057
  | 157 => 1022
  | 158 => 471
  | 159 => 800
  | 160 => 785
  | 161 => 486
  | 162 => 1099
  | 163 => 740
  | 164 => 357
  | 165 => 790
  | 166 => 455
  | 167 => 680
  | 168 => 345
  | 169 => 650
  | 170 => 459
  | 171 => 1036
  | 172 => 1169
  | 173 => 830
  | 174 => 375
  | 175 => 560
  | 176 => 865
  | 177 => 1162
  | 178 => 1211
  | 179 => 820
  | 180 => 537
  | 181 => 2054
  | 182 => 399
  | 183 => 760
  | 184 => 905
  | 185 => 890
  | 186 => 847
  | 187 => 860
  | 188 => 405
  | 189 => 1246
  | 190 => 1991
  | 191 => 576
  | 192 => 573
  | 193 => 3002
  | 194 => 507
  | 195 => 1204
  | 196 => 965
  | 197 => 870
  | 198 => 591
  | 199 => 1000
  | 200 => 597
  | 201 => 970
  | 202 => 995
  | 203 => 924
  | 204 => 925
  | 205 => 1358
  | 206 => 603
  | 207 => 2704
  | 208 => 2189
  | 209 => 850
  | 210 => 435
  | 211 => 1316
  | 212 => 633
  | 213 => 1030
  | 214 => 1055
  | 215 => 648
  | 216 => 1477
  | 217 => 1442
  | 218 => 483
  | 219 => 700
  | 220 => 845
  | 221 => 1070
  | 222 => 2743
  | 223 => 1568
  | 224 => 465
  | 225 => 1090
  | 226 => 1115
  | 227 => 1060
  | 228 => 681
  | 229 => 950
  | 230 => 687
  | 231 => 1288
  | 232 => 665
  | 233 => 1130
  | 234 => 699
  | 235 => 1484
  | 236 => 1165
  | 237 => 1078
  | 238 => 1631
  | 239 => 880
  | 240 => 561
  | 241 => 2662
  | 242 => 567
  | 243 => 3268
  | 244 => 1205
  | 245 => 1110
  | 246 => 1183
  | 247 => 1976
  | 248 => 1785
  | 249 => 1250
  | 250 => 2651
  | 251 => 1020
  | 252 => 753
  | 253 => 4142
  | 254 => 747
  | 255 => 512
  | 256 => 1757
  | 257 => 1554
  | 258 => 771
  | 259 => 1220
  | 260 => 1285
  | 261 => 1270
  | 262 => 1799
  | 263 => 1160
  | 264 => 789
  | 265 => 1274
  | 266 => 555
  | 267 => 1708
  | 268 => 1841
  | 269 => 1150
  | 270 => 807
  | 271 => 1040
  | 272 => 609
  | 273 => 1834
  | 274 => 875
  | 275 => 1140
  | 276 => 805
  | 277 => 3302
  | 278 => 663
  | 279 => 1240
  | 280 => 1001
  | 281 => 1290
  | 282 => 843
  | 283 => 1340
  | 284 => 849
  | 285 => 1390
  | 286 => 1415
  | 287 => 864
  | 288 => 1981
  | 289 => 1946
  | 290 => 651
  | 291 => 1876
  | 292 => 3113
  | 293 => 1806
  | 294 => 615
  | 295 => 1736
  | 296 => 837
  | 297 => 3058
  | 298 => 1859
  | 299 => 1100
  | _ => 1


lemma witness_pos_and_mod (n : ℕ) (hn : n < 300) : witness n > 0 ∧ (witness n - 1) % Nat.totient (witness n) = n := by
  interval_cases n <;> decide

/--
A268597 Conjecture: a(n) > 0 for all n.
-/
theorem oeis_268597_conjecture_0 (n : ℕ) : A268597 n > 0 := by
  by_cases hn : n < 300
  · have h_spec := witness_pos_and_mod n hn
    have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := ⟨witness n, h_spec⟩
    exact sInf_pos_of_nonempty h_nonempty (fun x hx => hx.1)
  · by_cases hp : (n + 1).Prime
    · have h_spec : (n + 1)^2 > 0 ∧ ((n + 1)^2 - 1) % Nat.totient ((n + 1)^2) = n := by
        have hp_gt : n + 1 ≥ 2 := hp.two_le
        have h_pos : (n + 1)^2 > 0 := by positivity
        refine ⟨h_pos, ?_⟩
        have h_tot : Nat.totient ((n + 1)^2) = (n + 1) * n := by
          rw [show (n+1)^2 = (n+1)^(1+1) by rfl]
          rw [Nat.totient_prime_pow_succ hp 1]
          rw [pow_one]
          have : n + 1 - 1 = n := by omega
          rw [this]
        rw [h_tot]
        have h1 : (n + 1)^2 - 1 = (n + 1) * n + n := by
          rw [sq]
          have h_expand : (n + 1) * (n + 1) = (n + 1) * n + n + 1 := by ring
          rw [h_expand]
          rfl
        rw [h1]
        rw [Nat.add_mod_left]
        have h2 : n < (n + 1) * n := by
          have : 2 ≤ n + 1 := hp_gt
          nlinarith
        exact Nat.mod_eq_of_lt h2
      have h_nonempty : { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }.Nonempty := ⟨(n + 1)^2, h_spec⟩
      exact sInf_pos_of_nonempty h_nonempty (fun x hx => hx.1)
    · sorry
