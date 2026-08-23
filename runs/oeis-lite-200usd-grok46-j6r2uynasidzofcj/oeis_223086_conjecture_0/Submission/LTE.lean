import FormalConjectures.Util.ProblemImports

open Nat

/-! LTE for `2^n ± 1` at the prime 3. -/

lemma two_pow_mod_three_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, hk⟩ := hn
  have : n = 2 * k := by simpa [two_mul] using hk
  rw [this, pow_mul]
  have : (4 : ℕ) % 3 = 1 := by decide
  simp [pow_mod, this]

lemma two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  have h1 : n % 2 = 1 := Nat.odd_iff.mp hn
  have : n = 2 * (n / 2) + 1 := (Nat.div_add_mod n 2).symm.trans (by rw [h1])
  rw [this, pow_succ, pow_mul, Nat.mul_mod, pow_mod]
  simp

lemma padicValNat_two_pow_sub_one_of_even {n : ℕ} (hn : Even n) (h0 : n ≠ 0) :
    padicValNat 3 (2 ^ n - 1) = 1 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hn
  have hn2 : n = 2 * k := by simpa [two_mul] using hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hk)
  have hrew : 2 ^ n - 1 = 4 ^ k - 1 := by
    rw [hn2, show (4 : ℕ) = 2 ^ 2 from by decide, ← pow_mul]
  rw [hrew]
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide : (1 : ℕ) < 4) (by decide : 3 ∣ 4 - 1) (by decide : ¬ 3 ∣ 4)
    hk0 odd_three
  have hv4 : padicValNat 3 (4 - 1) = 1 := by decide
  have hvk : padicValNat 3 k = padicValNat 3 n := by
    have h2 : 2 ≠ 0 := by decide
    rw [hn2, padicValNat.mul h2 hk0]
    have : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
    omega
  simpa [hv4, hvk] using h

lemma padicValNat_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) :
    padicValNat 3 (2 ^ n - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have hmod : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : 2 ^ n % 3 = 2 := two_pow_mod_three_odd hn
  have hge : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have : (2 ^ n - 1) % 3 = 1 := by
    have : 2 ^ n % 3 = 2 := hpow
    -- 2^n = 3q+2, so 2^n-1 = 3q+1
    have := Nat.div_add_mod (2 ^ n) 3
    rw [hpow] at this
    have hsub : 2 ^ n - 1 = 3 * (2 ^ n / 3) + 1 := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  omega

lemma padicValNat_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) :
    padicValNat 3 (2 ^ n + 1) = 1 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1)
    (by decide : 3 ∣ 2 + 1) (by decide : ¬ 3 ∣ 2) hn
  have hv : padicValNat 3 (2 + 1) = 1 := by decide
  simpa [hv] using h

lemma padicValNat_two_pow_add_one_of_even {n : ℕ} (hn : Even n) :
    padicValNat 3 (2 ^ n + 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have hmod : (2 ^ n + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have hpow : 2 ^ n % 3 = 1 := two_pow_mod_three_even hn
  have : (2 ^ n + 1) % 3 = 2 := by
    rw [Nat.add_mod, hpow]
  omega

/-- Combined form used after a true-max inverse block (`t' = 1`). -/
lemma padicValNat_two_pow_add_signed (n : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hn : n ≠ 0) :
    padicValNat 3 ((2 : ℤ) ^ n + ε).natAbs ≤ 1 + padicValNat 3 n := by
  rcases hε with rfl | rfl
  · -- ε = 1
    have : ((2 : ℤ) ^ n + 1).natAbs = 2 ^ n + 1 := by
      have : (0 : ℤ) ≤ 2 ^ n + 1 := by
        nlinarith [show (0 : ℤ) ≤ 2 ^ n from pow_nonneg (by decide) n]
      rw [Int.natAbs_of_nonneg this, Int.natCast_pow]
      norm_cast
    rw [this]
    by_cases hen : Even n
    · rw [padicValNat_two_pow_add_one_of_even hen]; omega
    · have hodd : Odd n := Nat.odd_iff_not_even.mpr hen
      rw [padicValNat_two_pow_add_one_of_odd hodd]
  · -- ε = -1
    have hpos : (1 : ℤ) < (2 : ℤ) ^ n := by
      have : 1 < 2 ^ n := Nat.one_lt_two_pow hn
      exact_mod_cast this
    have : ((2 : ℤ) ^ n + (-1)).natAbs = 2 ^ n - 1 := by
      rw [add_neg_eq, Int.natAbs_natCast_sub_of_nonneg]
      · norm_cast
      · exact Int.le_of_lt hpos
    -- wait, let's do this more carefully
    have : ((2 : ℤ) ^ n - 1).natAbs = 2 ^ n - 1 := by
      have : (0 : ℤ) ≤ 2 ^ n - 1 := by
        have : (1 : ℤ) ≤ 2 ^ n := by
          exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ n)
        linarith
      rw [Int.natAbs_of_nonneg this]
      norm_cast
    rw [show (2 : ℤ) ^ n + (-1) = (2 : ℤ) ^ n - 1 by ring, this]
    by_cases hen : Even n
    · rw [padicValNat_two_pow_sub_one_of_even hen hn]
    · have hodd : Odd n := Nat.odd_iff_not_even.mpr hen
      rw [padicValNat_two_pow_sub_one_of_odd hodd]; omega
