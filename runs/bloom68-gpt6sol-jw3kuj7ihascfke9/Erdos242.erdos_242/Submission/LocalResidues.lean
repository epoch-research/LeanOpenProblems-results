import Submission.Classification

/-!
# A quadratic-nonresidue sufficient criterion for a small first denominator

This proves a new *conditional* family for hard primes: if the second possible
first denominator `6*k+2` has a prime factor non-square modulo seven, then
`24*k+1` has a strictly ordered Erdős–Straus decomposition. The ordinary
mathematical proof that this condition is also necessary *at this particular
first denominator*, and its general residue-saturation extension, are in
`Submission/LocalResidues.md`. Nothing here proves the universal conjecture.
-/

namespace Erdos242

/-- The strict inequality on a type-II divisor can be removed when the
modulus is coprime to the first denominator: divisors on opposite sides of
`x` are exchanged by `e ↦ x²/e`, and `e=x` is impossible. This is an exact
residue-set identity, not an existence result. -/
theorem small_divisor_iff_divisor_of_coprime (a x : ℕ)
    (ha : 2 < a) (hx : 0 < x) (hax : a.Coprime x) :
    (∃ d : ℕ, 0 < d ∧ d < x ∧ d ∣ x ^ 2 ∧ a ∣ x + d) ↔
      ∃ e : ℕ, 0 < e ∧ e ∣ x ^ 2 ∧ a ∣ x + e := by
  constructor
  · rintro ⟨d, hd, hdx, hdsq, hadiv⟩
    exact ⟨d, hd, hdsq, hadiv⟩
  · rintro ⟨e, he, hesq, haex⟩
    by_cases hex : e < x
    · exact ⟨e, he, hex, hesq, haex⟩
    have hne : e ≠ x := by
      intro heq
      subst e
      have hdiv2x : a ∣ 2 * x := by simpa only [two_mul] using haex
      have hdiv2 : a ∣ 2 := hax.dvd_of_dvd_mul_right hdiv2x
      exact (Nat.not_dvd_of_pos_of_lt (by norm_num) ha) hdiv2
    have hxe : x < e := by omega
    let d := x ^ 2 / e
    have hed : e * d = x ^ 2 := Nat.mul_div_cancel' hesq
    have hdpos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
      rw [hd0] at hed
      nlinarith [hx]
    have hdlt : d < x := by
      by_contra h
      have hxd : x ≤ d := by omega
      have hbound : x ^ 2 < e * x := by
        simpa only [pow_two] using (Nat.mul_lt_mul_right hx).mpr hxe
      have hle : e * x ≤ e * d := Nat.mul_le_mul_left e hxd
      omega
    have hddvd : d ∣ x ^ 2 := by
      refine ⟨e, ?_⟩
      nlinarith [hed]
    have hae : a.Coprime e := by
      apply Nat.coprime_of_dvd
      intro q hq hqa hqe
      have hqxe : q ∣ x + e := dvd_trans hqa haex
      have hqx : q ∣ x := (Nat.dvd_add_iff_left hqe).mpr hqxe
      have hqcx : q.Coprime x := hax.of_dvd_left hqa
      exact (ne_of_gt hq.one_lt) (hqcx.eq_one_of_dvd hqx)
    have hkey : e * (x + d) = x * (x + e) := by nlinarith [hed]
    have hamul : a ∣ e * (x + d) := by
      rw [hkey]
      exact haex.mul_left x
    exact ⟨d, hdpos, hdlt, hddvd, hae.dvd_of_dvd_mul_left hamul⟩


/-- A positive factorization `6*k+2 = 2*r*t` with `r` a non-square modulo
seven explicitly gives a type-I divisor at the second possible first
denominator. Primality of `24*k+1` is not needed for this construction. -/
theorem hard_second_typeI_of_factor (k r t : ℕ)
    (hx : 6 * k + 2 = 2 * r * t)
    (hres : r % 7 = 3 ∨ r % 7 = 5 ∨ r % 7 = 6) :
    TypeI (24 * k + 1) (6 * k + 2) := by
  have ha : 4 * (6 * k + 2) - (24 * k + 1) = 7 := by omega
  have hr : 0 < r := by omega
  change ∃ c : ℕ, 0 < c ∧ c ∣ (6 * k + 2) ^ 2 ∧
    4 * (6 * k + 2) - (24 * k + 1) ∣ 4 * c + 1
  rw [ha]
  rcases hres with h3 | h5 | h6
  · refine ⟨4 * r, by positivity, ?_, ?_⟩
    · rw [hx]
      refine ⟨r * t * t, ?_⟩
      ring
    · omega
  · refine ⟨r, hr, ?_, ?_⟩
    · rw [hx]
      refine ⟨4 * r * t * t, ?_⟩
      ring
    · omega
  · refine ⟨2 * r, by positivity, ?_, ?_⟩
    · rw [hx]
      refine ⟨2 * r * t * t, ?_⟩
      ring
    · omega

/-- For `k>0`, the preceding divisor yields positive *strictly increasing*
denominators solving the fraction equation at `24*k+1`. -/
theorem good_hard_of_second_factor (k r t : ℕ) (hk : 0 < k)
    (hx : 6 * k + 2 = 2 * r * t)
    (hres : r % 7 = 3 ∨ r % 7 = 5 ∨ r % 7 = 6) :
    Good (24 * k + 1) := by
  apply good_of_typeI (24 * k + 1) (6 * k + 2) (by omega) (by omega) (by omega)
  exact hard_second_typeI_of_factor k r t hx hres

/-- If the second possible first denominator has a prime divisor with residue
`3`, `5` or `6` modulo seven, the ordered decomposition exists. -/
theorem good_hard_of_second_nonresidue_prime (k r : ℕ) (hk : 0 < k)
    (hr : r.Prime) (hrx : r ∣ 6 * k + 2)
    (hres : r % 7 = 3 ∨ r % 7 = 5 ∨ r % 7 = 6) :
    Good (24 * k + 1) := by
  have hrge : 3 ≤ r := by omega
  have hrnot2 : ¬ r ∣ 2 := Nat.not_dvd_of_pos_of_lt (by norm_num) (by omega)
  have hrr : r ∣ 2 * (3 * k + 1) := by
    simpa only [mul_add, mul_one, mul_assoc, mul_comm, mul_left_comm] using hrx
  have hrhalf : r ∣ 3 * k + 1 := ((hr.dvd_mul).mp hrr).resolve_left hrnot2
  rcases hrhalf with ⟨t, ht⟩
  apply good_hard_of_second_factor k r t hk
  · calc
      6 * k + 2 = 2 * (3 * k + 1) := by ring
      _ = 2 * (r * t) := by rw [ht]
      _ = 2 * r * t := by ring
  · exact hres

/-- This hard prime fails at its smallest first denominator, but succeeds
at its second first denominator by the new nonresidue-factor theorem. -/
theorem good_193_via_second_nonresidue : Good 193 := by
  have hprime : (5 : ℕ).Prime := by norm_num
  apply good_hard_of_second_nonresidue_prime 8 5 (by norm_num) hprime
  · norm_num
  · norm_num


/-- A new short first-denominator witness for `2521`: `a=23`, `x=636`,
`d=8`; the ordered denominators are `(636,70588,5611746)`. -/
theorem hard_2521_early_typeII : TypeII 2521 636 := by
  refine ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem good_2521_early : Good 2521 :=
  good_of_typeII 2521 636 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hard_2521_early_typeII

/-- `3049` has neither of the first two small-modulus witnesses, but its
`a=11` candidate `x=765` has `d=5`. -/
theorem hard_3049_third_typeII : TypeII 3049 765 := by
  refine ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩

theorem good_3049_third : Good 3049 :=
  good_of_typeII 3049 765 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hard_3049_third_typeII


/-- Satisfying the local nonresidue-free restrictions at `a=3,7,11,23`
is not a prime counterexample: `58921` has this type-II divisor at `a=19`. -/
theorem hard_58921_residual_typeII : TypeII 58921 14735 := by
  refine ⟨1225, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Deterministic arithmetic certificate for the four simultaneously active
small-denominator restrictions in the soluble prime `58921`. -/
theorem hard_58921_factor_data :
    (58921 : ℕ).Prime ∧ (14731 : ℕ).Prime ∧ (29 : ℕ).Prime ∧
    (127 : ℕ).Prime ∧ (1637 : ℕ).Prime ∧ (307 : ℕ).Prime ∧
    (14732 : ℕ) = 2 ^ 2 * 29 * 127 ∧
    (14733 : ℕ) = 3 ^ 2 * 1637 ∧
    (14736 : ℕ) = 2 ^ 4 * 3 * 307 ∧
    14731 % 3 = 1 ∧ 29 % 7 = 1 ∧ 127 % 7 = 1 ∧
    1637 % 11 = 9 ∧ 307 % 23 = 8 ∧ 58921 % 72 = 25 := by
  norm_num


theorem good_58921_residual : Good 58921 :=
  good_of_typeII 58921 14735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hard_58921_residual_typeII

end Erdos242
