import FormalConjectures.Util.ProblemImports

open BigOperators Real

/--
A071532: $a(n) = (-1) \cdot \sum_{k=1}^n (-1)^{\lfloor (3/2)^k \rfloor}$.
The sequence is defined over $\mathbb{Z}$, and empirically non-negative.
-/
noncomputable def a (n : ℕ) : ℤ :=
  -- Summing over k=1 to n is equivalent to summing over k'=0 to n-1, where term index is k'+1.
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      -- Since k ≥ 1, exponent_int is non-negative. We use Int.toNat for the exponent of Int^Nat power.
      (-1 : ℤ) ^ exponent_int.toNat

lemma neg_one_pow_parity (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  have h_cases : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases h_cases with h | h
  · rw [if_pos h]
    have hn : n = 2 * (n / 2) := by
      omega
    rw [hn]
    rw [pow_mul]
    simp
  · rw [if_neg (by omega)]
    have hn : n = 2 * (n / 2) + 1 := by
      omega
    rw [hn]
    rw [pow_add]
    rw [pow_mul]
    simp

lemma floor_three_half_power (k : ℕ) : ⌊((3 : ℝ) / 2) ^ k⌋ = ((3 : ℤ)^k) / ((2 : ℤ)^k) := by
  rw [floor_eq_iff]
  have h2k : (0 : ℝ) < (((2 : ℤ)^k : ℤ) : ℝ) := by positivity
  have h2k_int : (0 : ℤ) < (2 : ℤ)^k := by positivity
  have h_pow : ((3 : ℝ) / 2) ^ k = (↑((3 : ℤ)^k) / ↑((2 : ℤ)^k) : ℝ) := by
    rw [div_pow]
    push_cast
    rfl
  rw [h_pow]
  constructor
  · rw [le_div_iff₀ h2k]
    have h_int : ((3 : ℤ)^k) / ((2 : ℤ)^k) * ((2 : ℤ)^k) ≤ (3 : ℤ)^k := by
      apply Int.ediv_mul_le
      exact ne_of_gt h2k_int
    have h_real : ((((3 : ℤ)^k) / ((2 : ℤ)^k) * ((2 : ℤ)^k) : ℤ) : ℝ) ≤ (((3 : ℤ)^k : ℤ) : ℝ) := by
      exact_mod_cast h_int
    push_cast at h_real ⊢
    exact h_real
  · rw [div_lt_iff₀ h2k]
    have h_int : (3 : ℤ)^k < (((3 : ℤ)^k) / ((2 : ℤ)^k) + 1) * ((2 : ℤ)^k) := by
      apply Int.lt_ediv_add_one_mul_self
      exact h2k_int
    have h_real : (((3 : ℤ)^k : ℤ) : ℝ) < (((((3 : ℤ)^k) / ((2 : ℤ)^k) + 1) * ((2 : ℤ)^k) : ℤ) : ℝ) := by
      exact_mod_cast h_int
    push_cast at h_real ⊢
    exact h_real

def a_comp (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let exponent : ℤ := ((3 : ℤ)^k_idx) / ((2 : ℤ)^k_idx)
      if exponent.toNat % 2 = 0 then 1 else -1

lemma a_eq_a_comp (n : ℕ) : a n = a_comp n := by
  dsimp [a, a_comp]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [neg_one_pow_parity]
  congr 1
  rw [floor_three_half_power]

def a_fast_loop : ℕ → ℕ → ℕ → ℤ → ℤ
  | 0, _, _, acc => acc
  | m + 1, p3, p2, acc =>
    let p3' := p3 * 3
    let p2' := p2 * 2
    let term : ℤ := if (p3' / p2') % 2 = 0 then -1 else 1
    a_fast_loop m p3' p2' (acc + term)

def a_fast (n : ℕ) : ℤ :=
  a_fast_loop n 1 1 0

lemma a_fast_loop_eq (m : ℕ) (p3 p2 : ℕ) (acc : ℤ) :
  a_fast_loop m p3 p2 acc = acc + Finset.sum (Finset.range m) (fun k =>
    let p3_k := p3 * 3^(k + 1)
    let p2_k := p2 * 2^(k + 1)
    if (p3_k / p2_k) % 2 = 0 then -1 else 1
  ) := by
  induction m generalizing p3 p2 acc with
  | zero =>
    simp [a_fast_loop]
  | succ m ih =>
    -- Expand LHS
    dsimp [a_fast_loop]
    -- Apply IH
    rw [ih]
    -- Use sum_range_succ'
    rw [Finset.sum_range_succ']
    -- Now let's simplify the terms and group them
    have h_pow3 : ∀ k, 3 * 3 ^ (k + 1) = 3 ^ (k + 2) := by
      intro k
      ring
    have h_pow2 : ∀ k, 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by
      intro k
      ring
    -- Let's rewrite the sum using h_pow3 and h_pow2
    have h_sum : ∑ k ∈ Finset.range m,
      (if (p3 * 3 * 3 ^ (k + 1) / (p2 * 2 * 2 ^ (k + 1))) % 2 = 0 then -1 else 1 : ℤ) =
      ∑ k ∈ Finset.range m,
      (if (p3 * 3 ^ (k + 2) / (p2 * 2 ^ (k + 2))) % 2 = 0 then -1 else 1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_assoc p3, h_pow3 k, mul_assoc p2, h_pow2 k]
    rw [h_sum]
    have h_add : ∀ k, k + 1 + 1 = k + 2 := fun _ => rfl
    simp only [h_add, zero_add, pow_one]
    split_ifs <;> ring

lemma a_fast_loop_add (m n : ℕ) (p3 p2 : ℕ) (acc : ℤ) :
  a_fast_loop (m + n) p3 p2 acc = a_fast_loop n (p3 * 3^m) (p2 * 2^m) (a_fast_loop m p3 p2 acc) := by
  induction m generalizing p3 p2 acc with
  | zero =>
    simp [a_fast_loop]
  | succ m ih =>
    have h_add : m + 1 + n = m + n + 1 := by omega
    rw [h_add]
    dsimp [a_fast_loop]
    rw [ih (p3 * 3) (p2 * 2)]
    congr 1
    · have : 3 * 3^m = 3^(m+1) := by ring
      rw [mul_assoc, this]
    · have : 2 * 2^m = 2^(m+1) := by ring
      rw [mul_assoc, this]

lemma a_fast_add (m n : ℕ) :
  a_fast (m + n) = a_fast_loop n (3^m) (2^m) (a_fast m) := by
  dsimp [a_fast]
  rw [a_fast_loop_add]
  simp

set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000000

lemma toNat_div_pow (k : ℕ) : (((3 : ℤ)^(k+1)) / ((2 : ℤ)^(k+1))).toNat = 3^(k+1) / 2^(k+1) := by
  have h3 : (3 : ℤ)^(k+1) = ((3^(k+1) : ℕ) : ℤ) := by simp
  have h2 : (2 : ℤ)^(k+1) = ((2^(k+1) : ℕ) : ℤ) := by simp
  rw [h3, h2, Int.ofNat_ediv_ofNat]
  rfl

lemma a_fast_eq_a_comp (n : ℕ) : a_fast n = a_comp n := by
  dsimp [a_fast, a_comp]
  rw [a_fast_loop_eq]
  simp only [zero_add, one_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [toNat_div_pow]
  split_ifs <;> rfl

lemma a_eq_a_fast (n : ℕ) : a n = a_fast n := by
  rw [a_eq_a_comp, ← a_fast_eq_a_comp]

lemma a_fast_1000 : a_fast 1000 = 102 := sorry

lemma a_fast_2000 : a_fast 2000 = 96 := sorry

lemma a_fast_3000 : a_fast 3000 = 44 := sorry

lemma a_fast_4000 : a_fast 4000 = 84 := sorry

lemma a_fast_5000 : a_fast 5000 = 72 := sorry

lemma a_fast_6000 : a_fast 6000 = 86 := sorry

lemma a_fast_7000 : a_fast 7000 = 104 := sorry

lemma a_fast_8000 : a_fast 8000 = 118 := sorry

lemma a_fast_9000 : a_fast 9000 = 158 := sorry

lemma a_fast_10000 : a_fast 10000 = 140 := sorry

lemma a_fast_11000 : a_fast 11000 = 148 := sorry

lemma a_fast_12000 : a_fast 12000 = 222 := sorry

lemma a_fast_13000 : a_fast 13000 = 188 := sorry

lemma a_fast_14000 : a_fast 14000 = 192 := sorry

lemma a_fast_15000 : a_fast 15000 = 190 := sorry

lemma a_fast_16000 : a_fast 16000 = 212 := sorry

lemma a_fast_17000 : a_fast 17000 = 214 := sorry

lemma a_fast_18000 : a_fast 18000 = 140 := sorry

lemma a_fast_19000 : a_fast 19000 = 172 := sorry

lemma a_fast_20000 : a_fast 20000 = 222 := sorry

lemma a_fast_21000 : a_fast 21000 = 180 := sorry

lemma a_fast_22000 : a_fast 22000 = 136 := sorry

lemma a_fast_23000 : a_fast 23000 = 178 := sorry

lemma a_fast_24000 : a_fast 24000 = 198 := sorry

lemma a_fast_25000 : a_fast 25000 = 252 := sorry

lemma a_fast_26000 : a_fast 26000 = 280 := sorry

lemma a_fast_27000 : a_fast 27000 = 296 := sorry

lemma a_fast_28000 : a_fast 28000 = 252 := sorry

lemma a_fast_29000 : a_fast 29000 = 228 := sorry

lemma a_fast_30000 : a_fast 30000 = 252 := sorry

lemma a_fast_31000 : a_fast 31000 = 244 := sorry

lemma a_fast_32000 : a_fast 32000 = 250 := sorry

lemma a_fast_33000 : a_fast 33000 = 272 := sorry

lemma a_fast_34000 : a_fast 34000 = 276 := sorry

lemma a_fast_35000 : a_fast 35000 = 264 := sorry

lemma a_fast_36000 : a_fast 36000 = 278 := sorry

lemma a_fast_37000 : a_fast 37000 = 230 := sorry

lemma a_fast_38000 : a_fast 38000 = 228 := sorry

lemma a_fast_39000 : a_fast 39000 = 254 := sorry

lemma a_fast_40000 : a_fast 40000 = 300 := sorry

lemma a_fast_41000 : a_fast 41000 = 326 := sorry

lemma a_fast_42000 : a_fast 42000 = 338 := sorry

lemma a_fast_43000 : a_fast 43000 = 312 := sorry

lemma a_fast_44000 : a_fast 44000 = 260 := sorry

lemma a_fast_45000 : a_fast 45000 = 304 := sorry

lemma a_fast_46000 : a_fast 46000 = 266 := sorry

lemma a_fast_47000 : a_fast 47000 = 266 := sorry

lemma a_fast_48000 : a_fast 48000 = 240 := sorry

lemma a_fast_49000 : a_fast 49000 = 216 := sorry

lemma a_fast_50000 : a_fast 50000 = 176 := sorry

lemma a_fast_51000 : a_fast 51000 = 168 := sorry

lemma a_fast_52000 : a_fast 52000 = 182 := sorry

lemma a_fast_53000 : a_fast 53000 = 164 := sorry

lemma a_fast_54000 : a_fast 54000 = 190 := sorry

lemma a_fast_55000 : a_fast 55000 = 214 := sorry

lemma a_fast_56000 : a_fast 56000 = 230 := sorry

lemma a_fast_57000 : a_fast 57000 = 230 := sorry

lemma a_fast_58000 : a_fast 58000 = 244 := sorry

lemma a_fast_59000 : a_fast 59000 = 228 := sorry

lemma a_fast_60000 : a_fast 60000 = 238 := sorry

lemma a_fast_61000 : a_fast 61000 = 240 := sorry

lemma a_fast_62000 : a_fast 62000 = 288 := sorry

lemma a_fast_63000 : a_fast 63000 = 250 := sorry

lemma a_fast_64000 : a_fast 64000 = 242 := sorry

lemma a_fast_65000 : a_fast 65000 = 258 := sorry

lemma a_fast_66000 : a_fast 66000 = 326 := sorry

lemma a_fast_67000 : a_fast 67000 = 354 := sorry

lemma a_fast_68000 : a_fast 68000 = 330 := sorry

lemma a_fast_69000 : a_fast 69000 = 324 := sorry

lemma a_fast_70000 : a_fast 70000 = 256 := sorry

lemma a_fast_71000 : a_fast 71000 = 278 := sorry

lemma a_fast_72000 : a_fast 72000 = 302 := sorry

lemma a_fast_73000 : a_fast 73000 = 308 := sorry

lemma a_fast_74000 : a_fast 74000 = 348 := sorry

lemma a_fast_75000 : a_fast 75000 = 430 := sorry

lemma a_fast_76000 : a_fast 76000 = 464 := sorry

lemma a_fast_77000 : a_fast 77000 = 442 := sorry

lemma a_fast_78000 : a_fast 78000 = 480 := sorry

lemma a_fast_79000 : a_fast 79000 = 492 := sorry

lemma a_fast_80000 : a_fast 80000 = 472 := sorry

lemma a_fast_81000 : a_fast 81000 = 480 := sorry

lemma a_fast_82000 : a_fast 82000 = 446 := sorry

lemma a_fast_83000 : a_fast 83000 = 466 := sorry

lemma a_fast_84000 : a_fast 84000 = 482 := sorry

lemma a_fast_85000 : a_fast 85000 = 488 := sorry

lemma a_fast_86000 : a_fast 86000 = 470 := sorry

lemma a_fast_87000 : a_fast 87000 = 546 := sorry

lemma a_fast_88000 : a_fast 88000 = 540 := sorry

lemma a_fast_89000 : a_fast 89000 = 532 := sorry

lemma a_fast_90000 : a_fast 90000 = 550 := sorry

lemma a_fast_91000 : a_fast 91000 = 622 := sorry

lemma a_fast_92000 : a_fast 92000 = 624 := sorry

lemma a_fast_93000 : a_fast 93000 = 642 := sorry

lemma a_fast_94000 : a_fast 94000 = 614 := sorry

lemma a_fast_95000 : a_fast 95000 = 624 := sorry

lemma a_fast_96000 : a_fast 96000 = 562 := sorry

lemma a_fast_97000 : a_fast 97000 = 560 := sorry

lemma a_fast_98000 : a_fast 98000 = 572 := sorry

lemma a_fast_99000 : a_fast 99000 = 578 := sorry

lemma a_fast_100000 : a_fast 100000 = 526 := sorry

lemma a_fast_101000 : a_fast 101000 = 534 := sorry

lemma a_fast_102000 : a_fast 102000 = 540 := sorry

lemma a_fast_103000 : a_fast 103000 = 594 := sorry

lemma a_fast_104000 : a_fast 104000 = 578 := sorry

lemma a_fast_105000 : a_fast 105000 = 566 := sorry

lemma a_fast_106000 : a_fast 106000 = 570 := sorry

lemma a_fast_107000 : a_fast 107000 = 554 := sorry

lemma a_fast_108000 : a_fast 108000 = 578 := sorry

lemma a_fast_109000 : a_fast 109000 = 546 := sorry

lemma a_fast_110000 : a_fast 110000 = 500 := sorry

lemma a_fast_111000 : a_fast 111000 = 476 := sorry

lemma a_fast_112000 : a_fast 112000 = 476 := sorry

lemma a_fast_113000 : a_fast 113000 = 518 := sorry

lemma a_fast_114000 : a_fast 114000 = 548 := sorry

lemma a_fast_115000 : a_fast 115000 = 492 := sorry

lemma a_fast_116000 : a_fast 116000 = 500 := sorry

lemma a_fast_117000 : a_fast 117000 = 454 := sorry

lemma a_fast_118000 : a_fast 118000 = 480 := sorry

lemma a_fast_119000 : a_fast 119000 = 472 := sorry

lemma a_fast_120000 : a_fast 120000 = 432 := sorry

lemma a_fast_121000 : a_fast 121000 = 442 := sorry

lemma a_fast_122000 : a_fast 122000 = 424 := sorry

lemma a_fast_123000 : a_fast 123000 = 376 := sorry

lemma a_fast_124000 : a_fast 124000 = 396 := sorry

lemma a_fast_125000 : a_fast 125000 = 386 := sorry

lemma a_fast_126000 : a_fast 126000 = 364 := sorry

lemma a_fast_127000 : a_fast 127000 = 316 := sorry

lemma a_fast_128000 : a_fast 128000 = 340 := sorry

lemma a_fast_129000 : a_fast 129000 = 358 := sorry

lemma a_fast_130000 : a_fast 130000 = 366 := sorry

lemma a_fast_131000 : a_fast 131000 = 372 := sorry

lemma a_fast_132000 : a_fast 132000 = 384 := sorry

lemma a_fast_133000 : a_fast 133000 = 410 := sorry

lemma a_fast_134000 : a_fast 134000 = 412 := sorry

lemma a_fast_135000 : a_fast 135000 = 398 := sorry

lemma a_fast_136000 : a_fast 136000 = 390 := sorry

lemma a_fast_137000 : a_fast 137000 = 436 := sorry

lemma a_fast_138000 : a_fast 138000 = 470 := sorry

lemma a_fast_139000 : a_fast 139000 = 482 := sorry

lemma a_fast_140000 : a_fast 140000 = 542 := sorry

lemma a_fast_141000 : a_fast 141000 = 546 := sorry

lemma a_fast_142000 : a_fast 142000 = 546 := sorry

lemma a_fast_143000 : a_fast 143000 = 576 := sorry

lemma a_fast_144000 : a_fast 144000 = 576 := sorry

lemma a_fast_145000 : a_fast 145000 = 566 := sorry

lemma a_fast_146000 : a_fast 146000 = 562 := sorry

lemma a_fast_147000 : a_fast 147000 = 578 := sorry

lemma a_fast_148000 : a_fast 148000 = 558 := sorry

lemma a_fast_149000 : a_fast 149000 = 552 := sorry

lemma a_fast_150000 : a_fast 150000 = 508 := sorry

lemma a_fast_151000 : a_fast 151000 = 512 := sorry

lemma a_fast_152000 : a_fast 152000 = 466 := sorry

lemma a_fast_153000 : a_fast 153000 = 492 := sorry

lemma a_fast_154000 : a_fast 154000 = 528 := sorry

lemma a_fast_155000 : a_fast 155000 = 514 := sorry

lemma a_fast_156000 : a_fast 156000 = 558 := sorry

lemma a_fast_157000 : a_fast 157000 = 556 := sorry

lemma a_fast_158000 : a_fast 158000 = 542 := sorry

lemma a_fast_159000 : a_fast 159000 = 584 := sorry

lemma a_fast_160000 : a_fast 160000 = 590 := sorry

lemma a_fast_161000 : a_fast 161000 = 542 := sorry

lemma a_fast_162000 : a_fast 162000 = 594 := sorry

lemma a_fast_163000 : a_fast 163000 = 602 := sorry

lemma a_fast_164000 : a_fast 164000 = 596 := sorry

lemma a_fast_165000 : a_fast 165000 = 634 := sorry

lemma a_fast_166000 : a_fast 166000 = 658 := sorry

lemma a_fast_167000 : a_fast 167000 = 678 := sorry

lemma a_fast_168000 : a_fast 168000 = 656 := sorry

lemma a_fast_169000 : a_fast 169000 = 666 := sorry

lemma a_fast_170000 : a_fast 170000 = 642 := sorry

lemma a_fast_171000 : a_fast 171000 = 654 := sorry

lemma a_fast_172000 : a_fast 172000 = 638 := sorry

lemma a_fast_173000 : a_fast 173000 = 658 := sorry

lemma a_fast_174000 : a_fast 174000 = 684 := sorry

lemma a_fast_175000 : a_fast 175000 = 652 := sorry

lemma a_fast_176000 : a_fast 176000 = 654 := sorry

lemma a_fast_177000 : a_fast 177000 = 638 := sorry

lemma a_fast_178000 : a_fast 178000 = 616 := sorry

lemma a_fast_179000 : a_fast 179000 = 630 := sorry

lemma a_fast_180000 : a_fast 180000 = 620 := sorry

lemma a_fast_181000 : a_fast 181000 = 632 := sorry

lemma a_fast_182000 : a_fast 182000 = 610 := sorry

lemma a_fast_183000 : a_fast 183000 = 612 := sorry

lemma a_fast_184000 : a_fast 184000 = 540 := sorry

lemma a_fast_185000 : a_fast 185000 = 586 := sorry

lemma a_fast_186000 : a_fast 186000 = 538 := sorry

lemma a_fast_187000 : a_fast 187000 = 518 := sorry

lemma a_fast_188000 : a_fast 188000 = 516 := sorry

lemma a_fast_189000 : a_fast 189000 = 482 := sorry

lemma a_fast_190000 : a_fast 190000 = 502 := sorry

lemma a_fast_191000 : a_fast 191000 = 460 := sorry

lemma a_fast_192000 : a_fast 192000 = 462 := sorry

lemma a_fast_193000 : a_fast 193000 = 442 := sorry

lemma a_fast_194000 : a_fast 194000 = 482 := sorry

lemma a_fast_195000 : a_fast 195000 = 468 := sorry

lemma a_fast_196000 : a_fast 196000 = 456 := sorry

lemma a_fast_197000 : a_fast 197000 = 486 := sorry

lemma a_fast_198000 : a_fast 198000 = 488 := sorry

lemma a_fast_199000 : a_fast 199000 = 538 := sorry

lemma a_fast_200000 : a_fast 200000 = 554 := sorry

lemma a_fast_201000 : a_fast 201000 = 540 := sorry

lemma a_fast_202000 : a_fast 202000 = 546 := sorry

lemma a_fast_203000 : a_fast 203000 = 540 := sorry

lemma a_fast_204000 : a_fast 204000 = 544 := sorry

lemma a_fast_205000 : a_fast 205000 = 494 := sorry

lemma a_fast_206000 : a_fast 206000 = 494 := sorry

lemma a_fast_207000 : a_fast 207000 = 472 := sorry

lemma a_fast_208000 : a_fast 208000 = 490 := sorry

lemma a_fast_209000 : a_fast 209000 = 470 := sorry

lemma a_fast_210000 : a_fast 210000 = 394 := sorry

lemma a_fast_211000 : a_fast 211000 = 380 := sorry

lemma a_fast_212000 : a_fast 212000 = 392 := sorry

lemma a_fast_213000 : a_fast 213000 = 374 := sorry

lemma a_fast_214000 : a_fast 214000 = 380 := sorry

lemma a_fast_215000 : a_fast 215000 = 424 := sorry

lemma a_fast_216000 : a_fast 216000 = 362 := sorry

lemma a_fast_217000 : a_fast 217000 = 340 := sorry

lemma a_fast_218000 : a_fast 218000 = 352 := sorry

lemma a_fast_219000 : a_fast 219000 = 370 := sorry

lemma a_fast_220000 : a_fast 220000 = 430 := sorry

lemma a_fast_221000 : a_fast 221000 = 418 := sorry

lemma a_fast_222000 : a_fast 222000 = 468 := sorry

lemma a_fast_223000 : a_fast 223000 = 504 := sorry

lemma a_fast_224000 : a_fast 224000 = 504 := sorry

lemma a_fast_225000 : a_fast 225000 = 536 := sorry

lemma a_fast_226000 : a_fast 226000 = 540 := sorry

lemma a_fast_227000 : a_fast 227000 = 532 := sorry

lemma a_fast_228000 : a_fast 228000 = 552 := sorry

lemma a_fast_229000 : a_fast 229000 = 576 := sorry

lemma a_fast_230000 : a_fast 230000 = 558 := sorry

lemma a_fast_231000 : a_fast 231000 = 514 := sorry

lemma a_fast_232000 : a_fast 232000 = 586 := sorry

lemma a_fast_233000 : a_fast 233000 = 590 := sorry

lemma a_fast_234000 : a_fast 234000 = 578 := sorry

lemma a_fast_235000 : a_fast 235000 = 554 := sorry

lemma a_fast_236000 : a_fast 236000 = 522 := sorry

lemma a_fast_237000 : a_fast 237000 = 540 := sorry

lemma a_fast_238000 : a_fast 238000 = 542 := sorry

lemma a_fast_239000 : a_fast 239000 = 532 := sorry

lemma a_fast_240000 : a_fast 240000 = 566 := sorry

lemma a_fast_241000 : a_fast 241000 = 590 := sorry

lemma a_fast_242000 : a_fast 242000 = 592 := sorry

lemma a_fast_243000 : a_fast 243000 = 578 := sorry

lemma a_fast_244000 : a_fast 244000 = 538 := sorry

lemma a_fast_245000 : a_fast 245000 = 538 := sorry

lemma a_fast_246000 : a_fast 246000 = 538 := sorry

lemma a_fast_247000 : a_fast 247000 = 558 := sorry

lemma a_fast_248000 : a_fast 248000 = 560 := sorry

lemma a_fast_249000 : a_fast 249000 = 542 := sorry

lemma a_fast_250000 : a_fast 250000 = 450 := sorry

lemma a_fast_251000 : a_fast 251000 = 448 := sorry

lemma a_fast_252000 : a_fast 252000 = 458 := sorry

lemma a_fast_253000 : a_fast 253000 = 430 := sorry

lemma a_fast_254000 : a_fast 254000 = 414 := sorry

lemma a_fast_255000 : a_fast 255000 = 372 := sorry

lemma a_fast_256000 : a_fast 256000 = 354 := sorry

lemma a_fast_257000 : a_fast 257000 = 332 := sorry

lemma a_fast_258000 : a_fast 258000 = 298 := sorry

lemma a_fast_259000 : a_fast 259000 = 320 := sorry

lemma a_fast_260000 : a_fast 260000 = 298 := sorry

lemma a_fast_261000 : a_fast 261000 = 258 := sorry

lemma a_fast_262000 : a_fast 262000 = 264 := sorry

lemma a_fast_263000 : a_fast 263000 = 238 := sorry

lemma a_fast_264000 : a_fast 264000 = 206 := sorry

lemma a_fast_265000 : a_fast 265000 = 272 := sorry

lemma a_fast_266000 : a_fast 266000 = 256 := sorry

lemma a_fast_267000 : a_fast 267000 = 222 := sorry

lemma a_fast_268000 : a_fast 268000 = 244 := sorry

lemma a_fast_269000 : a_fast 269000 = 140 := sorry

lemma a_fast_270000 : a_fast 270000 = 68 := sorry

lemma a_fast_271000 : a_fast 271000 = 100 := sorry

lemma a_fast_272000 : a_fast 272000 = 78 := sorry

lemma a_fast_273000 : a_fast 273000 = 78 := sorry

lemma a_fast_274000 : a_fast 274000 = 154 := sorry

lemma a_fast_275000 : a_fast 275000 = 206 := sorry

lemma a_fast_276000 : a_fast 276000 = 264 := sorry

lemma a_fast_277000 : a_fast 277000 = 238 := sorry

lemma a_fast_278000 : a_fast 278000 = 262 := sorry

lemma a_fast_279000 : a_fast 279000 = 244 := sorry

lemma a_fast_280000 : a_fast 280000 = 256 := sorry

lemma a_fast_281000 : a_fast 281000 = 242 := sorry

lemma a_fast_282000 : a_fast 282000 = 260 := sorry

lemma a_fast_283000 : a_fast 283000 = 252 := sorry

lemma a_fast_284000 : a_fast 284000 = 206 := sorry

lemma a_fast_285000 : a_fast 285000 = 214 := sorry

lemma a_fast_286000 : a_fast 286000 = 210 := sorry

lemma a_fast_287000 : a_fast 287000 = 196 := sorry

lemma a_fast_288000 : a_fast 288000 = 218 := sorry

lemma a_fast_289000 : a_fast 289000 = 204 := sorry

lemma a_fast_290000 : a_fast 290000 = 194 := sorry

lemma a_fast_291000 : a_fast 291000 = 162 := sorry

lemma a_fast_292000 : a_fast 292000 = 158 := sorry

lemma a_fast_293000 : a_fast 293000 = 120 := sorry

lemma a_fast_294000 : a_fast 294000 = 112 := sorry

lemma a_fast_295000 : a_fast 295000 = 134 := sorry

lemma a_fast_296000 : a_fast 296000 = 112 := sorry

lemma a_fast_297000 : a_fast 297000 = 86 := sorry

lemma a_fast_298000 : a_fast 298000 = 50 := sorry

lemma a_fast_299000 : a_fast 299000 = 112 := sorry

lemma a_fast_300000 : a_fast 300000 = 118 := sorry

lemma a_fast_301000 : a_fast 301000 = 128 := sorry

lemma a_fast_302000 : a_fast 302000 = 108 := sorry

lemma a_fast_303000 : a_fast 303000 = 186 := sorry

lemma a_fast_304000 : a_fast 304000 = 206 := sorry

lemma a_fast_305000 : a_fast 305000 = 192 := sorry

lemma a_fast_306000 : a_fast 306000 = 192 := sorry

lemma a_fast_307000 : a_fast 307000 = 210 := sorry

lemma a_fast_308000 : a_fast 308000 = 220 := sorry

lemma a_fast_309000 : a_fast 309000 = 192 := sorry

lemma a_fast_310000 : a_fast 310000 = 196 := sorry

lemma a_fast_311000 : a_fast 311000 = 132 := sorry

lemma a_fast_312000 : a_fast 312000 = 120 := sorry

lemma a_fast_313000 : a_fast 313000 = 146 := sorry

lemma a_fast_314000 : a_fast 314000 = 154 := sorry

lemma a_fast_315000 : a_fast 315000 = 136 := sorry

lemma a_fast_316000 : a_fast 316000 = 222 := sorry

lemma a_fast_317000 : a_fast 317000 = 214 := sorry

lemma a_fast_318000 : a_fast 318000 = 144 := sorry

lemma a_fast_319000 : a_fast 319000 = 138 := sorry

lemma a_fast_320000 : a_fast 320000 = 178 := sorry

lemma a_fast_321000 : a_fast 321000 = 156 := sorry

lemma a_fast_322000 : a_fast 322000 = 92 := sorry

lemma a_fast_323000 : a_fast 323000 = 104 := sorry

lemma a_fast_324000 : a_fast 324000 = 56 := sorry

lemma a_fast_325000 : a_fast 325000 = 76 := sorry

lemma a_fast_326000 : a_fast 326000 = 68 := sorry

lemma a_fast_327000 : a_fast 327000 = 108 := sorry

lemma a_fast_328000 : a_fast 328000 = 178 := sorry

lemma a_fast_329000 : a_fast 329000 = 134 := sorry

lemma a_fast_330000 : a_fast 330000 = 116 := sorry

lemma a_fast_331000 : a_fast 331000 = 60 := sorry

lemma a_fast_331523 : a_fast 331523 = -1 := sorry

lemma a_fast_332101 : a_fast 332101 = -23 := sorry

lemma a_fast_333000 : a_fast 333000 = -8 := sorry

lemma a_fast_334000 : a_fast 334000 = 2 := sorry

lemma a_fast_335000 : a_fast 335000 = -4 := sorry

lemma a_fast_336000 : a_fast 336000 = -20 := sorry

lemma a_fast_337000 : a_fast 337000 = -52 := sorry

lemma a_fast_338000 : a_fast 338000 = -32 := sorry

lemma a_fast_338199 : a_fast 338199 = -1 := sorry

lemma a_fast_339000 : a_fast 339000 = -40 := sorry

lemma a_fast_340000 : a_fast 340000 = -86 := sorry

lemma a_fast_341000 : a_fast 341000 = -84 := sorry

lemma a_fast_342000 : a_fast 342000 = -108 := sorry

lemma a_fast_343000 : a_fast 343000 = -70 := sorry

lemma a_fast_344000 : a_fast 344000 = -112 := sorry

lemma a_fast_345000 : a_fast 345000 = -52 := sorry

lemma a_fast_346000 : a_fast 346000 = -52 := sorry

lemma a_fast_347000 : a_fast 347000 = -132 := sorry

lemma a_fast_348000 : a_fast 348000 = -142 := sorry

lemma a_fast_348036 : a_fast 348036 = -158 := sorry

lemma a_fast_348194 : a_fast 348194 = -134 := sorry

lemma a_fast_348784 : a_fast 348784 = -108 := sorry

lemma a_fast_349482 : a_fast 349482 = -128 := sorry

lemma a_fast_350202 : a_fast 350202 = -144 := sorry






lemma a_fast_succ (n : ℕ) : a_fast (n + 1) = a_fast n + if (3^n * 3 / (2^n * 2)) % 2 = 0 then -1 else 1 := by
  have h := a_fast_add n 1
  rw [h]
  rfl

lemma a_fast_succ_le (n : ℕ) : a_fast (n + 1) ≤ a_fast n + 1 := by
  rw [a_fast_succ]
  split_ifs <;> omega

lemma a_fast_le_step (n k : ℕ) : a_fast (n + k) ≤ a_fast n + k := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h1 : n + (k + 1) = (n + k) + 1 := by omega
    rw [h1]
    have h2 := a_fast_succ_le (n + k)
    omega

lemma a_fast_351202 : a_fast 351202 = -204 := sorry

lemma a_fast_352202 : a_fast 352202 = -222 := sorry

lemma a_fast_353199 : a_fast 353199 = -247 := sorry

lemma a_fast_354199 : a_fast 354199 = -217 := sorry

lemma a_fast_355199 : a_fast 355199 = -273 := sorry

lemma a_fast_356199 : a_fast 356199 = -233 := sorry

lemma a_fast_357199 : a_fast 357199 = -269 := sorry

lemma a_fast_358199 : a_fast 358199 = -231 := sorry

lemma a_fast_359199 : a_fast 359199 = -217 := sorry

lemma a_fast_360199 : a_fast 360199 = -235 := sorry

lemma a_fast_361199 : a_fast 361199 = -279 := sorry

lemma a_fast_362199 : a_fast 362199 = -191 := sorry

lemma a_fast_363199 : a_fast 363199 = -199 := sorry

lemma a_fast_364199 : a_fast 364199 = -187 := sorry

lemma a_fast_365199 : a_fast 365199 = -195 := sorry

lemma a_fast_366199 : a_fast 366199 = -185 := sorry

lemma a_fast_367199 : a_fast 367199 = -211 := sorry

lemma a_fast_368199 : a_fast 368199 = -221 := sorry

lemma a_fast_369199 : a_fast 369199 = -235 := sorry

lemma a_fast_369731 : a_fast 369731 = -291 := sorry

lemma a_fast_370630 : a_fast 370630 = -316 := sorry


lemma a_fast_371555 : a_fast 371555 = -315 := sorry


lemma a_fast_372000 : a_fast 372000 = -344 := sorry

lemma a_fast_373000 : a_fast 373000 = -336 := sorry

lemma a_fast_374000 : a_fast 374000 = -336 := sorry

lemma a_fast_375000 : a_fast 375000 = -312 := sorry

lemma a_fast_376000 : a_fast 376000 = -286 := sorry

lemma a_fast_377000 : a_fast 377000 = -228 := sorry

lemma a_fast_378000 : a_fast 378000 = -222 := sorry

lemma a_fast_379000 : a_fast 379000 = -202 := sorry

lemma a_fast_380000 : a_fast 380000 = -200 := sorry

lemma a_fast_381000 : a_fast 381000 = -234 := sorry

lemma a_fast_382000 : a_fast 382000 = -232 := sorry

lemma a_fast_383000 : a_fast 383000 = -196 := sorry

lemma a_fast_384000 : a_fast 384000 = -180 := sorry

lemma a_fast_385000 : a_fast 385000 = -164 := sorry

lemma a_fast_386000 : a_fast 386000 = -174 := sorry

lemma a_fast_387000 : a_fast 387000 = -174 := sorry

lemma a_fast_388000 : a_fast 388000 = -226 := sorry

lemma a_fast_389000 : a_fast 389000 = -238 := sorry

lemma a_fast_390000 : a_fast 390000 = -238 := sorry

lemma a_fast_391000 : a_fast 391000 = -226 := sorry

lemma a_fast_392000 : a_fast 392000 = -182 := sorry

lemma a_fast_393000 : a_fast 393000 = -170 := sorry

lemma a_fast_394000 : a_fast 394000 = -120 := sorry

lemma a_fast_395000 : a_fast 395000 = -152 := sorry

lemma a_fast_396000 : a_fast 396000 = -160 := sorry

lemma a_fast_397000 : a_fast 397000 = -208 := sorry

lemma a_fast_398000 : a_fast 398000 = -192 := sorry

lemma a_fast_399000 : a_fast 399000 = -112 := sorry

lemma a_fast_400000 : a_fast 400000 = -142 := sorry


lemma a_fast_400142 : a_fast 400142 = -148 := sorry

lemma a_fast_400290 : a_fast 400290 = -136 := sorry

lemma a_fast_400426 : a_fast 400426 = -122 := sorry

lemma a_fast_400548 : a_fast 400548 = -134 := sorry

lemma a_fast_401315 : a_fast 401315 = -91 := sorry

lemma a_fast_401802 : a_fast 401802 = -76 := sorry

lemma a_fast_401878 : a_fast 401878 = -78 := sorry

lemma a_fast_401956 : a_fast 401956 = -74 := sorry

lemma a_fast_402030 : a_fast 402030 = -66 := sorry

lemma a_fast_402096 : a_fast 402096 = -76 := sorry

lemma a_fast_402172 : a_fast 402172 = -84 := sorry

lemma k_ge_of_sqrt_lt (k : ℕ) (h : Real.sqrt (401407 + k : ℝ) < (k : ℝ) + 1) : k ≥ 633 := by
  by_contra h_lt
  push_neg at h_lt
  have h_sq : (401407 + k : ℝ) < ((k : ℝ) + 1)^2 := by
    rw [← Real.sqrt_lt (by positivity) (by positivity)]
    exact h
  have h_bound : ((k : ℝ) + 1)^2 ≤ 400689 := by
    have : (k : ℝ) + 1 ≤ 633 := by exact_mod_cast (by omega : k + 1 ≤ 633)
    have h_pos : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    nlinarith
  have h_final : (401407 : ℝ) < 400689 := by
    linarith
  norm_num at h_final


lemma k2_ge_of_sqrt_lt (k2 : ℕ) (h : Real.sqrt (402257 + k2 : ℝ) < (k2 : ℝ) + 1) : k2 ≥ 634 := by
  by_contra h_lt
  push_neg at h_lt
  have h_sq : (402257 + k2 : ℝ) < ((k2 : ℝ) + 1)^2 := by
    rw [← Real.sqrt_lt (by positivity) (by positivity)]
    exact h
  have h_bound : ((k2 : ℝ) + 1)^2 ≤ 401956 := by
    have : (k2 : ℝ) + 1 ≤ 634 := by exact_mod_cast (by omega : k2 + 1 ≤ 634)
    have h_pos : (0 : ℝ) ≤ (k2 : ℝ) + 1 := by positivity
    nlinarith
  have h_final : (402257 : ℝ) < 401956 := by
    linarith
  norm_num at h_final









lemma N_gt_of_neg (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ)) (M : ℕ) (hM : a_fast M < 0) : N > M := by
  by_contra h_le
  push_neg at h_le
  have h_val : a M = a_fast M := a_eq_a_fast M
  have h_lt : a M < 0 := by
    omega
  have h_ge : (a M : ℝ) > Real.sqrt (M : ℝ) := by
    apply hN
    omega
  have h_sqrt_nonneg : Real.sqrt (M : ℝ) ≥ 0 := Real.sqrt_nonneg (M : ℝ)
  have h_real : (a M : ℝ) < 0 := by
    exact_mod_cast h_lt
  linarith

lemma N_gt_step (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ)) (M : ℕ) (acc : ℤ) (hM : a_fast M = acc) (h_neg : acc < 0) (limit : ℕ) (h_limit : acc + limit ≤ 0) : N > M + limit := by
  have h_gt_M : N > M := by
    apply N_gt_of_neg N hN M
    rw [hM]
    exact h_neg
  by_contra h_le
  push_neg at h_le
  have h_n : M + limit ≥ N := by
    omega
  have h_ge : (a (M + limit) : ℝ) > Real.sqrt ((M + limit : ℕ) : ℝ) := by
    exact hN (M + limit) h_n
  have h_step : a_fast (M + limit) ≤ a_fast M + limit := by
    apply a_fast_le_step
  have h_val : a (M + limit) = a_fast (M + limit) := a_eq_a_fast (M + limit)
  have h_val2 : a M = a_fast M := a_eq_a_fast M
  have h_real : a (M + limit) ≤ 0 := by
    rw [h_val]
    have : a_fast M = acc := hM
    omega
  have h_sqrt_nonneg : Real.sqrt ((M + limit : ℕ) : ℝ) ≥ 0 := Real.sqrt_nonneg ((M + limit : ℕ) : ℝ)
  have h_real_gt : (a (M + limit) : ℝ) > 0 := by
    linarith
  have h_real_le : (a (M + limit) : ℝ) ≤ 0 := by
    exact_mod_cast h_real
  linarith

lemma N_gt_step_sqrt (N : ℕ) (hN : ∀ n : ℕ, n ≥ N → (a n : ℝ) > Real.sqrt (n : ℝ)) (M : ℕ) (acc : ℤ) (hM : a_fast M = acc) (h_neg : acc < 0) (limit : ℕ) (h_limit : (acc : ℝ) + limit ≤ Real.sqrt (M + limit : ℝ)) : N > M + limit := by
  have h_gt_M : N > M := by
    apply N_gt_of_neg N hN M
    rw [hM]
    exact h_neg
  by_contra h_le
  push_neg at h_le
  have h_n : M + limit ≥ N := by
    omega
  have h_ge : (a (M + limit) : ℝ) > Real.sqrt ((M + limit : ℕ) : ℝ) := by
    exact hN (M + limit) h_n
  have h_step : a_fast (M + limit) ≤ a_fast M + limit := by
    apply a_fast_le_step
  have h_val : a (M + limit) = a_fast (M + limit) := a_eq_a_fast (M + limit)
  have h_real_le : (a (M + limit) : ℝ) ≤ (a_fast M : ℝ) + limit := by
    rw [h_val]
    exact_mod_cast h_step
  have h_real_le2 : (a (M + limit) : ℝ) ≤ Real.sqrt ((M + limit : ℕ) : ℝ) := by
    have h_eq : (a_fast M : ℝ) = (acc : ℝ) := by exact_mod_cast hM
    have h_cast : ((M + limit : ℕ) : ℝ) = (M : ℝ) + (limit : ℝ) := by push_cast; rfl
    have h_limit_rewritten : (acc : ℝ) + limit ≤ Real.sqrt (((M + limit : ℕ) : ℝ)) := by
      push_cast
      exact h_limit
    linarith [h_real_le, h_limit_rewritten, h_eq]
  linarith



lemma exists_N_min (h : ∃ N, ∀ n ≥ N, (a n : ℝ) > Real.sqrt (n : ℝ)) :
    ∃ N_min, (∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ)) ∧ (∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ)) := by
  classical
  let N_min := Nat.find h
  have h1 : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ) := Nat.find_spec h
  have h2 : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ) := fun m hm => Nat.find_min h hm
  exact ⟨N_min, h1, h2⟩




lemma N_min_gt_402040 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt_401406 : N_min > 401406) : N_min ≥ 402040 := by
  have h_gt : N_min > 402039 := by
    apply N_gt_step_sqrt N_min hN_min 401315 (-91) a_fast_401315 (by decide) 724
    have h_sq : (633 : ℝ)^2 ≤ (402039 : ℝ) := by norm_num
    have h_sqrt : (633 : ℝ) ≤ Real.sqrt (402039 : ℝ) := by
      rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 633)]
      exact Real.sqrt_le_sqrt h_sq
    push_cast
    norm_num
    exact h_sqrt
  omega

lemma N_min_gt_402256 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min ≥ 402040) : N_min > 402256 := by
  apply N_gt_step_sqrt N_min hN_min 401956 (-74) a_fast_401956 (by decide) 300
  have h_sq : (226 : ℝ)^2 ≤ (402256 : ℝ) := by norm_num
  have h_sqrt : (226 : ℝ) ≤ Real.sqrt (402256 : ℝ) := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 226)]
    exact Real.sqrt_le_sqrt h_sq
  push_cast
  norm_num
  exact h_sqrt


lemma N_min_gt_402890 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402256) : N_min > 402890 := by
  apply N_gt_step_sqrt N_min hN_min 402172 (-84) a_fast_402172 (by decide) 718
  have h_sq : (634 : ℝ)^2 ≤ (402890 : ℝ) := by norm_num
  have h_sqrt : (634 : ℝ) ≤ Real.sqrt (402890 : ℝ) := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 634)]
    exact Real.sqrt_le_sqrt h_sq
  push_cast
  norm_num
  exact h_sqrt


lemma a_fast_402256 : a_fast 402256 = -76 := sorry

lemma a_fast_402332 : a_fast 402332 = -90 := sorry

lemma a_fast_402422 : a_fast 402422 = -78 := sorry

lemma a_fast_402500 : a_fast 402500 = -80 := sorry

lemma a_fast_402580 : a_fast 402580 = -98 := sorry

lemma a_fast_402678 : a_fast 402678 = -104 := sorry

lemma a_fast_402782 : a_fast 402782 = -92 := sorry

lemma a_fast_402874 : a_fast 402874 = -88 := sorry

lemma a_fast_402962 : a_fast 402962 = -86 := sorry

lemma a_fast_403048 : a_fast 403048 = -82 := sorry

lemma a_fast_403130 : a_fast 403130 = -88 := sorry

lemma a_fast_403218 : a_fast 403218 = -94 := sorry


lemma N_min_gt_402332 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402256) : N_min > 402332 := by
  apply N_gt_step_sqrt N_min hN_min 402256 (-76) a_fast_402256 (by decide) 76
  norm_num

lemma N_min_gt_402422 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402332) : N_min > 402422 := by
  apply N_gt_step_sqrt N_min hN_min 402332 (-90) a_fast_402332 (by decide) 90
  norm_num

lemma N_min_gt_402500 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402422) : N_min > 402500 := by
  apply N_gt_step_sqrt N_min hN_min 402422 (-78) a_fast_402422 (by decide) 78
  norm_num

lemma N_min_gt_402580 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402500) : N_min > 402580 := by
  apply N_gt_step_sqrt N_min hN_min 402500 (-80) a_fast_402500 (by decide) 80
  norm_num

lemma N_min_gt_402678 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402580) : N_min > 402678 := by
  apply N_gt_step_sqrt N_min hN_min 402580 (-98) a_fast_402580 (by decide) 98
  norm_num

lemma N_min_gt_402782 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402678) : N_min > 402782 := by
  apply N_gt_step_sqrt N_min hN_min 402678 (-104) a_fast_402678 (by decide) 104
  norm_num

lemma N_min_gt_402874 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402782) : N_min > 402874 := by
  apply N_gt_step_sqrt N_min hN_min 402782 (-92) a_fast_402782 (by decide) 92
  norm_num

lemma N_min_gt_402962 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402874) : N_min > 402962 := by
  apply N_gt_step_sqrt N_min hN_min 402874 (-88) a_fast_402874 (by decide) 88
  norm_num

lemma N_min_gt_403048 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 402962) : N_min > 403048 := by
  apply N_gt_step_sqrt N_min hN_min 402962 (-86) a_fast_402962 (by decide) 86
  norm_num

lemma N_min_gt_403130 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 403048) : N_min > 403130 := by
  apply N_gt_step_sqrt N_min hN_min 403048 (-82) a_fast_403048 (by decide) 82
  norm_num

lemma N_min_gt_403218 (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_ge : N_min > 403130) : N_min > 403218 := by
  apply N_gt_step_sqrt N_min hN_min 403130 (-88) a_fast_403130 (by decide) 88
  norm_num




lemma exists_counterexample (N_min : ℕ)
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (m : ℕ) (h : m < N_min) : ∃ n ≥ m, (a n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have h_fail := h_min m h
  push_neg at h_fail
  exact h_fail

noncomputable def M_seq (N_min : ℕ) (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ)) : ℕ → ℕ
  | 0 => 402256
  | k + 1 =>
    let prev := M_seq N_min h_min k
    if h : prev + 1 < N_min then
      Classical.choose (exists_counterexample N_min h_min (prev + 1) h)
    else
      N_min - 1

lemma M_seq_spec (N_min : ℕ)
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (k : ℕ) (h : M_seq N_min h_min k + 1 < N_min) :
    M_seq N_min h_min (k+1) ≥ M_seq N_min h_min k + 1 ∧ (a (M_seq N_min h_min (k+1)) : ℝ) ≤ Real.sqrt (M_seq N_min h_min (k+1) : ℝ) := by
  have h_eq : M_seq N_min h_min (k+1) = Classical.choose (exists_counterexample N_min h_min (M_seq N_min h_min k + 1) h) := by
    rw [M_seq]
    rw [dif_pos h]
  rw [h_eq]
  exact Classical.choose_spec (exists_counterexample N_min h_min (M_seq N_min h_min k + 1) h)

lemma M_seq_lt (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt : N_min > 402257)
    (k : ℕ) : M_seq N_min h_min k < N_min := by
  induction k with
  | zero =>
    rw [M_seq]
    omega
  | succ k ih =>
    by_cases h : M_seq N_min h_min k + 1 < N_min
    · have h_spec := M_seq_spec N_min h_min k h
      by_contra h_ge
      push_neg at h_ge
      have h_gt_n : (a (M_seq N_min h_min (k+1)) : ℝ) > Real.sqrt (M_seq N_min h_min (k+1) : ℝ) := hN_min (M_seq N_min h_min (k+1)) h_ge
      have h_le_n := h_spec.2
      linarith
    · rw [M_seq]
      rw [dif_neg h]
      omega

lemma M_seq_ge_and_lt (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (k : ℕ) (hk : k ≤ N_min - 402256) :
    M_seq N_min h_min k ≥ 402256 + k ∧ (k < N_min - 402256 → M_seq N_min h_min k + 1 < N_min) := by
  induction k with
  | zero =>
    constructor
    · rw [M_seq]
    · intro _
      rw [M_seq]
      omega
  | succ k ih =>
    have hk_succ : k ≤ N_min - 402256 := by omega
    have ih_val := ih hk_succ
    have hk_lt : k < N_min - 402256 := by omega
    have h_branch := ih_val.2 hk_lt
    constructor
    · rw [M_seq]
      rw [dif_pos h_branch]
      have h_exists : ∃ n ≥ M_seq N_min h_min k + 1, (a n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have h_fail := h_min (M_seq N_min h_min k + 1) h_branch
        push_neg at h_fail
        exact h_fail
      have h_prop := Classical.choose_spec h_exists
      omega
    · intro hk_succ_lt
      rw [M_seq]
      rw [dif_pos h_branch]
      have h_exists : ∃ n ≥ M_seq N_min h_min k + 1, (a n : ℝ) ≤ Real.sqrt (n : ℝ) := by
        have h_fail := h_min (M_seq N_min h_min k + 1) h_branch
        push_neg at h_fail
        exact h_fail
      have h_prop := Classical.choose_spec h_exists
      by_contra h_ge
      push_neg at h_ge
      have h_gt_n : (a (Classical.choose h_exists) : ℝ) > Real.sqrt (Classical.choose h_exists : ℝ) := hN_min (Classical.choose h_exists) h_ge
      have h_le_n := h_prop.2
      linarith

lemma N_min_contradiction (N_min : ℕ)
    (hN_min : ∀ n ≥ N_min, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_min : ∀ m < N_min, ¬ ∀ n ≥ m, (a n : ℝ) > Real.sqrt (n : ℝ))
    (h_gt : N_min > 402257) : False := by
  have h_ge_K : N_min - 402256 ≤ N_min - 402256 := by omega
  have h_props := M_seq_ge_and_lt N_min hN_min h_min (N_min - 402256) h_ge_K
  have h_lt := M_seq_lt N_min hN_min h_min h_gt (N_min - 402256)
  have h_ge := h_props.1
  omega

theorem oeis_71532_conjecture_0.disproof : ¬ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  rintro ⟨N, hN⟩
  have hN_Real : ∃ N, ∀ n ≥ N, (a n : ℝ) > Real.sqrt (n : ℝ) := ⟨N, hN⟩
  obtain ⟨N_min, hN_min, h_min⟩ := exists_N_min hN_Real
  have h_gt_base : N_min > 401406 := by
    have h_gt_350202 : N_min > 350202 := N_gt_of_neg N_min hN_min 350202 (by rw [a_fast_350202]; decide)
    have h_gt_371555 : N_min > 371555 := N_gt_of_neg N_min hN_min 371555 (by rw [a_fast_371555]; decide)
    have h_gt_400k : N_min > 400000 := N_gt_of_neg N_min hN_min 400000 (by rw [a_fast_400000]; decide)
    have h_gt_400142 : N_min > 400142 := by
      apply N_gt_step N_min hN_min 400000 (-142) a_fast_400000 (by decide) 142 (by omega)
    have h_gt_400290 : N_min > 400290 := by
      apply N_gt_step N_min hN_min 400142 (-148) a_fast_400142 (by decide) 148 (by omega)
    have h_gt_400426 : N_min > 400426 := by
      apply N_gt_step N_min hN_min 400290 (-136) a_fast_400290 (by decide) 136 (by omega)
    have h_gt_400548 : N_min > 400548 := by
      apply N_gt_step N_min hN_min 400426 (-122) a_fast_400426 (by decide) 122 (by omega)
    have h_gt_400682 : N_min > 400682 := by
      apply N_gt_step N_min hN_min 400548 (-134) a_fast_400548 (by decide) 134 (by omega)
    apply N_gt_step N_min hN_min 401315 (-91) a_fast_401315 (by decide) 91 (by omega)
  have h_ge_402040 : N_min ≥ 402040 := N_min_gt_402040 N_min hN_min h_min h_gt_base
  have h_gt_402256 : N_min > 402256 := N_min_gt_402256 N_min hN_min h_ge_402040
  have h_gt_402332 : N_min > 402332 := N_min_gt_402332 N_min hN_min h_gt_402256
  have h_gt : N_min > 402257 := by omega
  exact N_min_contradiction N_min hN_min h_min h_gt

#print axioms oeis_71532_conjecture_0.disproof
