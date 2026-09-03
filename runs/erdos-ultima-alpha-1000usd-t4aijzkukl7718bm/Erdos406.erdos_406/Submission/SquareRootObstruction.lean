import Submission.GeneralResidueObstruction

/-! Even squares with unrestricted powers-of-two divisibility can still have
only ternary digits zero and one. The examples have the odd divisor five and
therefore do not disprove Erdős 406. -/

namespace Erdos406Work

lemma nine_pow_two_pow_odd_quotient (k : ℕ) :
    ∃ q : ℕ, Odd q ∧ 9 ^ (2 ^ k) = 1 + 2 ^ (k + 3) * q := by
  induction k with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ k ih =>
    obtain ⟨q, hq, he⟩ := ih
    refine ⟨q + 2 ^ (k + 2) * q ^ 2, ?_, ?_⟩
    · apply hq.add_even
      exact (even_two.pow_of_ne_zero (by omega : k + 2 ≠ 0)).mul_right _
    · rw [pow_succ, pow_mul, he]
      simp only [pow_succ]
      ring

/-- Powers of nine can lift any such affine root through all powers of two,
without decreasing the exponent. -/
lemma affine_nine_pow_divisible (a b B k : ℕ) (hb : Odd b) (hab : 8 ∣ a + b) :
    ∃ j : ℕ, B ≤ j ∧ 2 ^ (k + 3) ∣ a + b * 9 ^ j := by
  induction k with
  | zero =>
    refine ⟨B, le_rfl, ?_⟩
    have hp : Nat.ModEq 8 (9 ^ B) 1 := by
      simpa only [one_pow] using (show Nat.ModEq 8 9 1 by decide).pow B
    have hh : Nat.ModEq 8 (a + b * 9 ^ B) (a + b) := by
      simpa only [mul_one] using (hp.mul_left b).add_left a
    exact Nat.modEq_zero_iff_dvd.mp (hh.trans (Nat.modEq_zero_iff_dvd.mpr hab))
  | succ k ih =>
    obtain ⟨j, hBj, t, ht⟩ := ih
    by_cases ht2 : Even t
    · refine ⟨j, hBj, ?_⟩
      obtain ⟨u, hu⟩ := ht2
      refine ⟨u, ?_⟩
      rw [ht, hu]
      simp only [pow_succ]
      ring
    · obtain ⟨q, hq, he⟩ := nine_pow_two_pow_odd_quotient k
      have hto : Odd t := Nat.not_even_iff_odd.mp ht2
      have heven : Even (t + b * 9 ^ j * q) :=
        hto.add_odd ((hb.mul ((by decide : Odd (9 : ℕ)).pow)).mul hq)
      obtain ⟨u, hu⟩ := heven
      refine ⟨j + 2 ^ k, hBj.trans (Nat.le_add_right j _), u, ?_⟩
      have hcalc : a + b * 9 ^ (j + 2 ^ k) =
          2 ^ (k + 3) * (t + b * 9 ^ j * q) := by
        rw [pow_add, he]
        nlinarith [ht]
      rw [hcalc, hu]
      simp only [pow_succ]
      ring

lemma square_block_coefficients_good :
    Nat.digits 3 (8035 ^ 2) ⊆ [0, 1] ∧
    Nat.digits 3 (2 * 8035 * 11645) ⊆ [0, 1] ∧
    Nat.digits 3 (11645 ^ 2) ⊆ [0, 1] := by
  decide +kernel

lemma good_square_affine_nine (j : ℕ) (hj : 9 ≤ j) :
    Nat.digits 3 ((8035 + 11645 * 9 ^ j) ^ 2) ⊆ [0, 1] := by
  obtain ⟨ha, hab, hb⟩ := square_block_coefficients_good
  have hL : 18 ≤ 2 * j := by omega
  have hp : 3 ^ 18 ≤ 3 ^ (2 * j) := Nat.pow_le_pow_right (by decide) hL
  have hltab : 2 * 8035 * 11645 < 3 ^ (2 * j) := by
    exact lt_of_lt_of_le (by decide) hp
  have hlta : 8035 ^ 2 < 3 ^ (2 * j) := by
    exact lt_of_lt_of_le (by decide) hp
  have hh := good_add_shifted hlta ha (good_add_shifted hltab hab hb)
  have he : (8035 + 11645 * 9 ^ j) ^ 2 =
      8035 ^ 2 + 3 ^ (2 * j) * (2 * 8035 * 11645 + 3 ^ (2 * j) * 11645 ^ 2) := by
    rw [show (9 : ℕ) = 3 ^ 2 by decide, pow_mul]
    ring
  rwa [he]

lemma bad_square_root_affine_nine (j : ℕ) (hj : 1 ≤ j) :
    ¬ Nat.digits 3 (8035 + 11645 * 9 ^ j) ⊆ [0, 1] := by
  intro hg
  have hh := (digits_iff_no_carries _).mp hg 2
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  norm_num [pow_succ, Nat.add_mod, Nat.mul_mod] at hh

/-- Arbitrarily large good even squares whose roots are divisible by any fixed
power of two, coprime to three, and have a fixed odd divisor. -/
lemma arbitrary_guard_good_square (K B : ℕ) :
    ∃ n : ℕ, B < n ∧ 2 ^ K ∣ n ∧ n % 3 = 1 ∧
      Nat.digits 3 (n ^ 2) ⊆ [0, 1] ∧ ¬ Nat.digits 3 n ⊆ [0, 1] ∧ 5 ∣ n ∧
      ¬ n.isPowerOfTwo ∧ ¬ (n ^ 2).isPowerOfTwo := by
  obtain ⟨j, hj, hd⟩ := affine_nine_pow_divisible 8035 11645 (B + 9) K
    (by decide) (by decide)
  let n := 8035 + 11645 * 9 ^ j
  have hn5 : 5 ∣ n := by
    dsimp [n]
    exact dvd_add (by decide) (dvd_mul_of_dvd_left (by decide) _)
  have hnlarge : B < n := by
    have hp : j < 9 ^ j := Nat.lt_pow_self (by decide)
    dsimp [n]
    omega
  refine ⟨n, hnlarge, (pow_dvd_pow 2 (by omega : K ≤ K + 3)).trans hd,
    ?_, good_square_affine_nine j (by omega),
    bad_square_root_affine_nine j (by omega), hn5, ?_, ?_⟩
  · have hjpos : 0 < j := by omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
    simp [n, pow_succ, Nat.add_mod, Nat.mul_mod]
  · rintro ⟨k, hk⟩
    rw [hk] at hn5
    have hh := Nat.prime_five.dvd_of_dvd_pow hn5
    norm_num at hh
  · rintro ⟨k, hk⟩
    have hh : 5 ∣ n ^ 2 := hn5.trans (dvd_pow_self n (by decide : 2 ≠ 0))
    rw [hk] at hh
    have h2 := Nat.prime_five.dvd_of_dvd_pow hh
    norm_num at h2

#print axioms arbitrary_guard_good_square
end Erdos406Work
