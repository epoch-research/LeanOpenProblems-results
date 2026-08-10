import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k
  let R_sq := Finset.range (n.sqrt + 1)
  let R_binom := Finset.range (n + 1)
  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

theorem not2sq_of_mod4 {m : ℕ} (h : m % 4 = 3) : ¬ ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, rfl⟩
  have hmod : ∀ z : ℕ, z ^ 2 % 4 = (z % 4) ^ 2 % 4 := fun z => by rw [Nat.pow_mod]
  have hsmall : ∀ r : ℕ, r < 4 → r ^ 2 % 4 = 0 ∨ r ^ 2 % 4 = 1 := by decide
  have hx := hmod x; have hy := hmod y
  have h4x := hsmall (x % 4) (Nat.mod_lt _ (by norm_num))
  have h4y := hsmall (y % 4) (Nat.mod_lt _ (by norm_num))
  omega

theorem not2sq_two_mul {k : ℕ} (hk : ¬ ∃ x y : ℕ, k = x ^ 2 + y ^ 2) :
    ¬ ∃ x y : ℕ, 2 * k = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  apply hk
  have hx2 : x ^ 2 % 2 = x % 2 := by
    rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one x with h'|h' <;> simp [h']
  have hy2 : y ^ 2 % 2 = y % 2 := by
    rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one y with h'|h' <;> simp [h']
  rcases le_total y x with hle | hle
  · obtain ⟨b, hb⟩ : ∃ b, x = y + 2 * b := ⟨(x - y) / 2, by omega⟩
    refine ⟨y + b, b, ?_⟩
    have h2 : 2 * k = 2 * ((y + b) ^ 2 + b ^ 2) := by rw [hb] at h; rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  · obtain ⟨b, hb⟩ : ∃ b, y = x + 2 * b := ⟨(y - x) / 2, by omega⟩
    refine ⟨x + b, b, ?_⟩
    have h2 : 2 * k = 2 * ((x + b) ^ 2 + b ^ 2) := by rw [hb] at h; rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem not2sq_pow2_mul (v t : ℕ) (ht : t % 4 = 3) :
    ¬ ∃ x y : ℕ, 2 ^ v * t = x ^ 2 + y ^ 2 := by
  induction v with
  | zero => simpa using not2sq_of_mod4 ht
  | succ nn ih =>
    have h2 : 2 ^ (nn + 1) * t = 2 * (2 ^ nn * t) := by ring
    rw [h2]; exact not2sq_two_mul ih

theorem not2sq_prime1 {m p : ℕ} (hp : p.Prime) (h3 : p % 4 = 3)
    (hd : p ∣ m) (hnd : ¬ p ^ 2 ∣ m) : ¬ ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨x, y, rfl⟩
  have hz : (x : ZMod p) ^ 2 = - (y : ZMod p) ^ 2 := by
    have h0 : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact hd
    push_cast at h0; linear_combination h0
  by_cases hx : (x : ZMod p) = 0
  · have hy : (y : ZMod p) = 0 := by
      have hyy : (y : ZMod p) ^ 2 = 0 := by
        rw [hx, zero_pow (by norm_num)] at hz; linear_combination hz
      exact pow_eq_zero_iff (by norm_num) |>.mp hyy
    apply hnd
    obtain ⟨a, rfl⟩ := (ZMod.natCast_eq_zero_iff x p).mp hx
    obtain ⟨b, rfl⟩ := (ZMod.natCast_eq_zero_iff y p).mp hy
    exact ⟨a ^ 2 + b ^ 2, by ring⟩
  · exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq hx hz) h3

theorem notrep_prime (s1 s2 p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3)
    (hd : p ∣ (800322180 - s1 - s2)) (hnd : ¬ p ^ 2 ∣ (800322180 - s1 - s2))
    (x y : ℕ) (h : x ^ 2 + y ^ 2 + s1 + s2 = 800322180) : False := by
  have he : x ^ 2 + y ^ 2 = 800322180 - s1 - s2 := by omega
  exact not2sq_prime1 hp h3 hd hnd ⟨x, y, he.symm⟩

theorem notrep_pow2 (s1 s2 v t : ℕ) (ht : t % 4 = 3)
    (hm : 2 ^ v * t = 800322180 - s1 - s2)
    (x y : ℕ) (h : x ^ 2 + y ^ 2 + s1 + s2 = 800322180) : False := by
  have he : x ^ 2 + y ^ 2 = 800322180 - s1 - s2 := by omega
  rw [← hm] at he
  exact not2sq_pow2_mul v t ht ⟨x, y, he.symm⟩

theorem Bmono : Monotone (fun k => (2 * k + 1).choose k) := by
  apply monotone_nat_of_le_succ
  intro k
  calc (2 * k + 1).choose k
      ≤ (2 * k + 1).choose k + (2 * k + 1).choose (k + 1) := Nat.le_add_right _ _
    _ = (2 * k + 1 + 1).choose (k + 1) := (Nat.choose_succ_succ (2 * k + 1) k).symm
    _ ≤ (2 * k + 1 + 1).choose k + (2 * k + 1 + 1).choose (k + 1) := Nat.le_add_left _ _
    _ = (2 * k + 1 + 1 + 1).choose (k + 1) := (Nat.choose_succ_succ (2 * k + 1 + 1) k).symm
    _ = (2 * (k + 1) + 1).choose (k + 1) := by ring_nf


theorem prime_3 : Nat.Prime 3 := by norm_num
theorem prime_7 : Nat.Prime 7 := by norm_num
theorem prime_11 : Nat.Prime 11 := by norm_num
theorem prime_19 : Nat.Prime 19 := by norm_num
theorem prime_23 : Nat.Prime 23 := by norm_num
theorem prime_31 : Nat.Prime 31 := by norm_num
theorem prime_43 : Nat.Prime 43 := by norm_num
theorem prime_59 : Nat.Prime 59 := by norm_num
theorem prime_67 : Nat.Prime 67 := by norm_num
theorem prime_139 : Nat.Prime 139 := by norm_num
theorem prime_163 : Nat.Prime 163 := by norm_num
theorem prime_223 : Nat.Prime 223 := by norm_num
theorem prime_227 : Nat.Prime 227 := by norm_num
theorem prime_467 : Nat.Prime 467 := by norm_num
theorem prime_563 : Nat.Prime 563 := by norm_num
theorem prime_647 : Nat.Prime 647 := by norm_num
theorem prime_719 : Nat.Prime 719 := by norm_num
theorem prime_2819 : Nat.Prime 2819 := by norm_num

theorem hB0 : (2 * 0 + 1).choose 0 = 1 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB1 : (2 * 1 + 1).choose 1 = 3 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB2 : (2 * 2 + 1).choose 2 = 10 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB3 : (2 * 3 + 1).choose 3 = 35 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB4 : (2 * 4 + 1).choose 4 = 126 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB5 : (2 * 5 + 1).choose 5 = 462 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB6 : (2 * 6 + 1).choose 6 = 1716 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB7 : (2 * 7 + 1).choose 7 = 6435 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB8 : (2 * 8 + 1).choose 8 = 24310 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB9 : (2 * 9 + 1).choose 9 = 92378 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB10 : (2 * 10 + 1).choose 10 = 352716 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB11 : (2 * 11 + 1).choose 11 = 1352078 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB12 : (2 * 12 + 1).choose 12 = 5200300 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB13 : (2 * 13 + 1).choose 13 = 20058300 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB14 : (2 * 14 + 1).choose 14 = 77558760 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hB15 : (2 * 15 + 1).choose 15 = 300540195 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide
theorem hBval16 : (2 * 16 + 1).choose 16 = 1166803110 := by rw [Nat.choose_eq_descFactorial_div_factorial]; decide

set_option maxHeartbeats 1000000 in
theorem key (x y i j : ℕ) (hij : i ≤ j) (hj : j ≤ 15)
    (heq : x ^ 2 + y ^ 2 + (2 * i + 1).choose i + (2 * j + 1).choose j = 800322180) : False := by
  have hi : i ≤ 15 := le_trans hij hj
  interval_cases i <;> interval_cases j <;>
    simp only [hB0, hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8, hB9, hB10, hB11, hB12, hB13, hB14, hB15] at heq
  exact notrep_prime 1 1 647 prime_647 rfl ⟨1236974, rfl⟩ (by decide) x y heq
  exact notrep_prime 1 3 163 prime_163 rfl ⟨4909952, rfl⟩ (by decide) x y heq
  exact notrep_prime 1 10 67 prime_67 rfl ⟨11945107, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1 35 5 25010067 rfl rfl x y heq
  exact notrep_prime 1 126 23 prime_23 rfl ⟨34796611, rfl⟩ (by decide) x y heq
  exact notrep_prime 1 462 467 prime_467 rfl ⟨1713751, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1 1716 0 800320463 rfl rfl x y heq
  exact notrep_pow2 1 6435 5 25009867 rfl rfl x y heq
  exact notrep_prime 1 24310 7 prime_7 rfl ⟨114328267, rfl⟩ (by decide) x y heq
  exact notrep_prime 1 92378 3 prime_3 rfl ⟨266743267, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1 352716 0 799969463 rfl rfl x y heq
  exact notrep_prime 1 1352078 3 prime_3 rfl ⟨266323367, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1 5200300 0 795121879 rfl rfl x y heq
  exact notrep_pow2 1 20058300 0 780263879 rfl rfl x y heq
  exact notrep_pow2 1 77558760 0 722763419 rfl rfl x y heq
  exact notrep_pow2 1 300540195 5 15618187 rfl rfl x y heq
  exact notrep_pow2 3 3 1 400161087 rfl rfl x y heq
  exact notrep_pow2 3 10 0 800322167 rfl rfl x y heq
  exact notrep_pow2 3 35 1 400161071 rfl rfl x y heq
  exact notrep_pow2 3 126 0 800322051 rfl rfl x y heq
  exact notrep_pow2 3 462 0 800321715 rfl rfl x y heq
  exact notrep_prime 3 1716 3 prime_3 rfl ⟨266773487, rfl⟩ (by decide) x y heq
  exact notrep_pow2 3 6435 1 400157871 rfl rfl x y heq
  exact notrep_pow2 3 24310 0 800297867 rfl rfl x y heq
  exact notrep_pow2 3 92378 0 800229799 rfl rfl x y heq
  exact notrep_prime 3 352716 3 prime_3 rfl ⟨266656487, rfl⟩ (by decide) x y heq
  exact notrep_pow2 3 1352078 0 798970099 rfl rfl x y heq
  exact notrep_prime 3 5200300 11 prime_11 rfl ⟨72283807, rfl⟩ (by decide) x y heq
  exact notrep_prime 3 20058300 3 prime_3 rfl ⟨260087959, rfl⟩ (by decide) x y heq
  exact notrep_prime 3 77558760 3 prime_3 rfl ⟨240921139, rfl⟩ (by decide) x y heq
  exact notrep_pow2 3 300540195 1 249890991 rfl rfl x y heq
  exact notrep_pow2 10 10 4 50020135 rfl rfl x y heq
  exact notrep_pow2 10 35 0 800322135 rfl rfl x y heq
  exact notrep_pow2 10 126 2 200080511 rfl rfl x y heq
  exact notrep_pow2 10 462 2 200080427 rfl rfl x y heq
  exact notrep_pow2 10 1716 1 400160227 rfl rfl x y heq
  exact notrep_pow2 10 6435 0 800315735 rfl rfl x y heq
  exact notrep_prime 10 24310 19 prime_19 rfl ⟨42120940, rfl⟩ (by decide) x y heq
  exact notrep_prime 10 92378 3 prime_3 rfl ⟨266743264, rfl⟩ (by decide) x y heq
  exact notrep_pow2 10 352716 1 399984727 rfl rfl x y heq
  exact notrep_pow2 10 1352078 2 199742523 rfl rfl x y heq
  exact notrep_pow2 10 5200300 1 397560935 rfl rfl x y heq
  exact notrep_pow2 10 20058300 1 390131935 rfl rfl x y heq
  exact notrep_prime 10 77558760 2819 prime_2819 rfl ⟨256390, rfl⟩ (by decide) x y heq
  exact notrep_pow2 10 300540195 0 499781975 rfl rfl x y heq
  exact notrep_pow2 35 35 1 400161055 rfl rfl x y heq
  exact notrep_pow2 35 126 0 800322019 rfl rfl x y heq
  exact notrep_pow2 35 462 0 800321683 rfl rfl x y heq
  exact notrep_prime 35 1716 43 prime_43 rfl ⟨18612103, rfl⟩ (by decide) x y heq
  exact notrep_pow2 35 6435 1 400157855 rfl rfl x y heq
  exact notrep_pow2 35 24310 0 800297835 rfl rfl x y heq
  exact notrep_pow2 35 92378 0 800229767 rfl rfl x y heq
  exact notrep_prime 35 352716 7 prime_7 rfl ⟨114281347, rfl⟩ (by decide) x y heq
  exact notrep_pow2 35 1352078 0 798970067 rfl rfl x y heq
  exact notrep_prime 35 5200300 3 prime_3 rfl ⟨265040615, rfl⟩ (by decide) x y heq
  exact notrep_prime 35 20058300 23 prime_23 rfl ⟨33924515, rfl⟩ (by decide) x y heq
  exact notrep_prime 35 77558760 23 prime_23 rfl ⟨31424495, rfl⟩ (by decide) x y heq
  exact notrep_pow2 35 300540195 1 249890975 rfl rfl x y heq
  exact notrep_prime 126 126 3 prime_3 rfl ⟨266773976, rfl⟩ (by decide) x y heq
  exact notrep_pow2 126 462 3 100040199 rfl rfl x y heq
  exact notrep_prime 126 1716 719 prime_719 rfl ⟨1113102, rfl⟩ (by decide) x y heq
  exact notrep_pow2 126 6435 0 800315619 rfl rfl x y heq
  exact notrep_prime 126 24310 563 prime_563 rfl ⟨1421488, rfl⟩ (by decide) x y heq
  exact notrep_pow2 126 92378 2 200057419 rfl rfl x y heq
  exact notrep_prime 126 352716 7 prime_7 rfl ⟨114281334, rfl⟩ (by decide) x y heq
  exact notrep_pow2 126 1352078 3 99871247 rfl rfl x y heq
  exact notrep_prime 126 5200300 7 prime_7 rfl ⟨113588822, rfl⟩ (by decide) x y heq
  exact notrep_prime 126 20058300 3 prime_3 rfl ⟨260087918, rfl⟩ (by decide) x y heq
  exact notrep_pow2 126 77558760 1 361381647 rfl rfl x y heq
  exact notrep_pow2 126 300540195 0 499781859 rfl rfl x y heq
  exact notrep_prime 462 462 7 prime_7 rfl ⟨114331608, rfl⟩ (by decide) x y heq
  exact notrep_prime 462 1716 3 prime_3 rfl ⟨266773334, rfl⟩ (by decide) x y heq
  exact notrep_pow2 462 6435 0 800315283 rfl rfl x y heq
  exact notrep_pow2 462 24310 6 12504647 rfl rfl x y heq
  exact notrep_pow2 462 92378 2 200057335 rfl rfl x y heq
  exact notrep_prime 462 352716 3 prime_3 rfl ⟨266656334, rfl⟩ (by decide) x y heq
  exact notrep_prime 462 1352078 7 prime_7 rfl ⟨114138520, rfl⟩ (by decide) x y heq
  exact notrep_prime 462 5200300 7 prime_7 rfl ⟨113588774, rfl⟩ (by decide) x y heq
  exact notrep_prime 462 20058300 3 prime_3 rfl ⟨260087806, rfl⟩ (by decide) x y heq
  exact notrep_pow2 462 77558760 1 361381479 rfl rfl x y heq
  exact notrep_pow2 462 300540195 0 499781523 rfl rfl x y heq
  exact notrep_pow2 1716 1716 2 200079687 rfl rfl x y heq
  exact notrep_prime 1716 6435 19 prime_19 rfl ⟨42121791, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 24310 7 prime_7 rfl ⟨114328022, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1716 92378 1 400114043 rfl rfl x y heq
  exact notrep_prime 1716 352716 3 prime_3 rfl ⟨266655916, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 1352078 139 prime_139 rfl ⟨5747974, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 5200300 227 prime_227 rfl ⟨3502732, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 20058300 11 prime_11 rfl ⟨70932924, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 77558760 7 prime_7 rfl ⟨103251672, rfl⟩ (by decide) x y heq
  exact notrep_prime 1716 300540195 67 prime_67 rfl ⟨7459407, rfl⟩ (by decide) x y heq
  exact notrep_pow2 6435 6435 1 400154655 rfl rfl x y heq
  exact notrep_pow2 6435 24310 0 800291435 rfl rfl x y heq
  exact notrep_pow2 6435 92378 0 800223367 rfl rfl x y heq
  exact notrep_prime 6435 352716 31 prime_31 rfl ⟨25805259, rfl⟩ (by decide) x y heq
  exact notrep_pow2 6435 1352078 0 798963667 rfl rfl x y heq
  exact notrep_prime 6435 5200300 139 prime_139 rfl ⟨5720255, rfl⟩ (by decide) x y heq
  exact notrep_prime 6435 20058300 3 prime_3 rfl ⟨260085815, rfl⟩ (by decide) x y heq
  exact notrep_prime 6435 77558760 3 prime_3 rfl ⟨240918995, rfl⟩ (by decide) x y heq
  exact notrep_pow2 6435 300540195 1 249887775 rfl rfl x y heq
  exact notrep_pow2 24310 24310 3 100034195 rfl rfl x y heq
  exact notrep_prime 24310 92378 3 prime_3 rfl ⟨266735164, rfl⟩ (by decide) x y heq
  exact notrep_prime 24310 352716 223 prime_223 rfl ⟨3587198, rfl⟩ (by decide) x y heq
  exact notrep_prime 24310 1352078 3 prime_3 rfl ⟨266315264, rfl⟩ (by decide) x y heq
  exact notrep_prime 24310 5200300 59 prime_59 rfl ⟨13476230, rfl⟩ (by decide) x y heq
  exact notrep_prime 24310 20058300 11 prime_11 rfl ⟨70930870, rfl⟩ (by decide) x y heq
  exact notrep_pow2 24310 77558760 1 361369555 rfl rfl x y heq
  exact notrep_pow2 24310 300540195 0 499757675 rfl rfl x y heq
  exact notrep_prime 92378 92378 19 prime_19 rfl ⟨42112496, rfl⟩ (by decide) x y heq
  exact notrep_pow2 92378 352716 1 399938543 rfl rfl x y heq
  exact notrep_pow2 92378 1352078 2 199719431 rfl rfl x y heq
  exact notrep_pow2 92378 5200300 1 397514751 rfl rfl x y heq
  exact notrep_pow2 92378 20058300 1 390085751 rfl rfl x y heq
  exact notrep_prime 92378 77558760 19 prime_19 rfl ⟨38035318, rfl⟩ (by decide) x y heq
  exact notrep_pow2 92378 300540195 0 499689607 rfl rfl x y heq
  exact notrep_pow2 352716 352716 2 199904187 rfl rfl x y heq
  exact notrep_prime 352716 1352078 19 prime_19 rfl ⟨42032494, rfl⟩ (by decide) x y heq
  exact notrep_pow2 352716 5200300 2 198692291 rfl rfl x y heq
  exact notrep_pow2 352716 20058300 2 194977791 rfl rfl x y heq
  exact notrep_prime 352716 77558760 19 prime_19 rfl ⟨38021616, rfl⟩ (by decide) x y heq
  exact notrep_prime 352716 300540195 19 prime_19 rfl ⟨26285751, rfl⟩ (by decide) x y heq
  exact notrep_prime 1352078 1352078 7 prime_7 rfl ⟨113945432, rfl⟩ (by decide) x y heq
  exact notrep_prime 1352078 5200300 3 prime_3 rfl ⟨264589934, rfl⟩ (by decide) x y heq
  exact notrep_prime 1352078 20058300 19 prime_19 rfl ⟨40995358, rfl⟩ (by decide) x y heq
  exact notrep_pow2 1352078 77558760 1 360705671 rfl rfl x y heq
  exact notrep_pow2 1352078 300540195 0 498429907 rfl rfl x y heq
  exact notrep_pow2 5200300 5200300 2 197480395 rfl rfl x y heq
  exact notrep_pow2 5200300 20058300 2 193765895 rfl rfl x y heq
  exact notrep_pow2 5200300 77558760 4 44847695 rfl rfl x y heq
  exact notrep_prime 5200300 300540195 19 prime_19 rfl ⟨26030615, rfl⟩ (by decide) x y heq
  exact notrep_pow2 20058300 20058300 2 190051395 rfl rfl x y heq
  exact notrep_pow2 20058300 77558760 5 21959535 rfl rfl x y heq
  exact notrep_prime 20058300 300540195 3 prime_3 rfl ⟨159907895, rfl⟩ (by decide) x y heq
  exact notrep_prime 77558760 77558760 3 prime_3 rfl ⟨215068220, rfl⟩ (by decide) x y heq
  exact notrep_prime 77558760 300540195 3 prime_3 rfl ⟨140741075, rfl⟩ (by decide) x y heq
  exact notrep_pow2 300540195 300540195 1 99620895 rfl rfl x y heq

theorem no_rep : ∀ x y c d : ℕ, c ≤ d →
    x ^ 2 + y ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d ≠ 800322180 := by
  intro x y c d hcd heq
  have hbd : (2 * d + 1).choose d ≤ 800322180 := by omega
  have hd15 : d ≤ 15 := by
    by_contra hh; push_neg at hh
    have hmono := Bmono (show 16 ≤ d by omega)
    simp only at hmono
    rw [hBval16] at hmono
    omega
  exact key x y c d hcd hd15 heq

theorem oeis_303639_conjecture_0.disproof : ¬ ∀ (n : ℕ), n > 1 → a n > 0 := by
  intro H
  have hpos := H 800322180 (by norm_num)
  have hzero : a 800322180 = 0 := by
    unfold a
    simp only []
    apply Finset.sum_eq_zero; intro x _
    apply Finset.sum_eq_zero; intro y _
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro d _
    apply if_neg
    rintro ⟨_, hcd, heq⟩
    exact no_rep x y c d hcd heq
  omega
