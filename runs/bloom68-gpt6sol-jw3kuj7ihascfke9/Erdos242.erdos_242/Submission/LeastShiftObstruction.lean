import Submission.SmallShiftRigidity
import Submission.PointwiseJacobi

/-!
# A least nonresidue-factor shift that fails the complete shifted Type-II axis

For the hard prime `p=2784961` the first `u>0` such that `p+u` has a
quadratic-nonresidue prime factor is `u=10`. Both nonresidue prime factors of
`p+10` fail to give a Type-II modular witness, even allowing all `d ∣ m²`.
The first eligible multiples of *both* factors fail Type I and Type II.
Nevertheless a different first denominator has an ordered Type-I solution.

The pointwise counterexample refutes only these concrete intermediary
constructions, not the Erdős–Straus conjecture or all possible uses of
minimality. This file does not import or modify `Submission.Spec`.
-/

namespace Erdos242
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem prime_2784961_nonresidue_factors : (2784961).Prime ∧ (191).Prime ∧ (2083).Prime ∧
    jacobiSym (191 : ℤ) 2784961 = -1 ∧
    jacobiSym (2083 : ℤ) 2784961 = -1 := by
  norm_num

theorem shift_ten_possible_moduli (m : ℕ) (hm : 0 < m) (hshift : 4 * m - 1 ∣ 2784961 + 10) :
    m = 2 ∨ m = 48 ∨ m = 521 ∨ m = 696243 := by
  have hdvd : 4 * m - 1 ∣ 7 * (191 * 2083) := by
    simpa only [show 2784961 + 10 = 7 * (191 * 2083) by norm_num] using hshift
  obtain ⟨a, bc, ha, hbc, habc⟩ := exists_dvd_and_dvd_of_dvd_mul hdvd
  obtain ⟨b, c, hb, hc, hbc'⟩ := exists_dvd_and_dvd_of_dvd_mul hbc
  have ha' : a = 1 ∨ a = 7 := (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd _ ha
  have hb' : b = 1 ∨ b = 191 := (by norm_num : Nat.Prime 191).eq_one_or_self_of_dvd _ hb
  have hc' : c = 1 ∨ c = 2083 := (by norm_num : Nat.Prime 2083).eq_one_or_self_of_dvd _ hc
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;>
    rcases hc' with rfl | rfl <;> subst bc <;> omega

theorem shift_ten_reject_191 : ∀ d : ℕ, d ∣ 48 ^ 2 → ¬ (191 ∣ 2784961 + 4 * d) := by
  intro d hd hdmod
  have hfactor : 48 ^ 2 = 2 ^ 8 * 3 ^ 2 := by norm_num
  rw [hfactor] at hd
  obtain ⟨a, b, ha, hb, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hd
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp ha
  obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hb
  have hdform : d = 2 ^ i * 3 ^ j := by rw [hab, hai, hbj]
  rw [hdform] at hdmod
  interval_cases i <;> interval_cases j <;> norm_num at hdmod

theorem shift_ten_reject_7 (d : ℕ) (hd : d ∣ 2 ^ 2) : ¬ (7 ∣ 2784961 + 4 * d) := by
  intro hdiv
  have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at *

theorem shift_ten_reject_2083 (d : ℕ) (hd : d ∣ 521 ^ 2) :
    ¬ (2083 ∣ 2784961 + 4 * d) := by
  intro hdiv
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 521)).mp hd
  interval_cases i <;> norm_num at hdiv

theorem shift_ten_no_full_typeII_factor :
    ¬ ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧ 4 * d < 2784961 ∧
       4 * m - 1 ∣ 2784961 + 10 ∧ 4 * m - 1 ∣ 2784961 + 4 * d := by
  rintro ⟨m, d, hm, _, hdsq, hsmall, hshift, hcert⟩
  rcases shift_ten_possible_moduli m hm hshift with rfl | rfl | rfl | rfl
  · exact shift_ten_reject_7 d (by simpa using hdsq) (by simpa using hcert)
  · exact shift_ten_reject_191 d (by simpa using hdsq) (by simpa using hcert)
  · exact shift_ten_reject_2083 d (by simpa using hdsq) (by simpa using hcert)
  · have hcert' : 2784971 ∣ 2784961 + 4 * d := by simpa using hcert
    obtain ⟨t, ht⟩ := hcert'
    omega


private theorem first_191_no_divisor (c : ℕ) (hc : c ∣ 696386 ^ 2) :
    ¬ (583 ∣ 4 * c + 1) ∧ ¬ (583 ∣ 696386 + c) := by
  have hfactor : 696386 ^ 2 = 2 ^ 2 * (191 ^ 2 * 1823 ^ 2) := by norm_num
  rw [hfactor] at hc
  obtain ⟨a, bc, ha, hbc, habc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  obtain ⟨b, c', hb, hc', hbc'⟩ := exists_dvd_and_dvd_of_dvd_mul hbc
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp ha
  obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 191)).mp hb
  obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 1823)).mp hc'
  have hcform : c = 2 ^ i * (191 ^ j * 1823 ^ k) := by
    rw [habc, hbc', hai, hbj, hck]
  rw [hcform]
  constructor <;> intro hdiv <;>
    interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num at hdiv

private theorem first_2083_no_divisor (c : ℕ) (hc : c ∣ 697805 ^ 2) :
    ¬ (6259 ∣ 4 * c + 1) ∧ ¬ (6259 ∣ 697805 + c) := by
  have hfactor : 697805 ^ 2 = 5 ^ 2 * (67 ^ 2 * 2083 ^ 2) := by norm_num
  rw [hfactor] at hc
  obtain ⟨a, bc, ha, hbc, habc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  obtain ⟨b, c', hb, hc', hbc'⟩ := exists_dvd_and_dvd_of_dvd_mul hbc
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp ha
  obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 67)).mp hb
  obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2083)).mp hc'
  have hcform : c = 5 ^ i * (67 ^ j * 2083 ^ k) := by
    rw [habc, hbc', hai, hbj, hck]
  rw [hcform]
  constructor <;> intro hdiv <;>
    interval_cases i <;> interval_cases j <;> interval_cases k <;> norm_num at hdiv

theorem first_shift_ten_nonresidue_multiples_fail :
    ¬ TypeI 2784961 696386 ∧ ¬ TypeII 2784961 696386 ∧
    ¬ TypeI 2784961 697805 ∧ ¬ TypeII 2784961 697805 := by
  have ha1 : 4 * 696386 - 2784961 = 583 := by norm_num
  have ha2 : 4 * 697805 - 2784961 = 6259 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨c, _, hc, hmod⟩
    exact (first_191_no_divisor c hc).1 (by simpa only [ha1] using hmod)
  · rintro ⟨d, _, _, hd, hmod⟩
    exact (first_191_no_divisor d hd).2 (by simpa only [ha1] using hmod)
  · rintro ⟨c, _, hc, hmod⟩
    exact (first_2083_no_divisor c hc).1 (by simpa only [ha2] using hmod)
  · rintro ⟨d, _, _, hd, hmod⟩
    exact (first_2083_no_divisor d hd).2 (by simpa only [ha2] using hmod)

private theorem no_types_first_0 :
    ¬ TypeI 2784961 696241 ∧ ¬ TypeII 2784961 696241 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696241 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696241 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696241 : ℕ) = 7 ^ 2 * (13 * 1093) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 7 (by norm_num : (2 : ℕ) ≠ 0), (by norm_num : Nat.Prime 7).primeFactors, (by norm_num : Nat.Prime 13).primeFactors, (by norm_num : Nat.Prime 1093).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696241
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

private theorem no_types_first_1 :
    ¬ TypeI 2784961 696242 ∧ ¬ TypeII 2784961 696242 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696242 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696242 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696242 : ℕ) = 2 * (337 * 1033) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 337).primeFactors, (by norm_num : Nat.Prime 1033).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696242
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

private theorem no_types_first_2 :
    ¬ TypeI 2784961 696243 ∧ ¬ TypeII 2784961 696243 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696243 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696243 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696243 : ℕ) = 3 * (232081) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 232081).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696243
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

private theorem no_types_first_3 :
    ¬ TypeI 2784961 696244 ∧ ¬ TypeII 2784961 696244 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696244 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696244 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696244 : ℕ) = 2 ^ 2 * (174061) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 2 (by norm_num : (2 : ℕ) ≠ 0), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 174061).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696244
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

private theorem no_types_first_4 :
    ¬ TypeI 2784961 696245 ∧ ¬ TypeII 2784961 696245 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696245 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696245 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696245 : ℕ) = 5 * (11 * (12659)) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 5).primeFactors, (by norm_num : Nat.Prime 11).primeFactors, (by norm_num : Nat.Prime 12659).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696245
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

private theorem no_types_first_5 :
    ¬ TypeI 2784961 696246 ∧ ¬ TypeII 2784961 696246 := by
  have hres : ∀ ell : ℕ, ell.Prime → ell ∣ 696246 →
      jacobiSym (ell : ℤ) 2784961 = 1 := by
    intro ell hp hd
    have hmem : ell ∈ (696246 : ℕ).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩
    have hf : (696246 : ℕ) = 2 * (3 * (116041)) := by norm_num
    rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 116041).primeFactors] at hmem
    simp only [Finset.mem_union, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h <;> subst ell <;> norm_num
  exact no_types_if_prime_factors_residue 2784961 696246
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hres

theorem first_six_fibers_fail_and_escape :
    (2784961).Prime ∧ 2784961 % 24 = 1 ∧
      (∀ j : ℕ, j < 6 →
       ¬ TypeI 2784961 (696241 + j) ∧ ¬ TypeII 2784961 (696241 + j)) ∧
      TypeI 2784961 696247 ∧ Good 2784961 := by
  have htype : TypeI 2784961 696247 := by
    refine ⟨7823, by norm_num, by norm_num, by norm_num⟩
  refine ⟨by norm_num, by norm_num, ?_, htype, ?_⟩
  · intro j hj
    interval_cases j
    · simpa using no_types_first_0
    · simpa using no_types_first_1
    · simpa using no_types_first_2
    · simpa using no_types_first_3
    · simpa using no_types_first_4
    · simpa using no_types_first_5
  · exact good_of_typeI 2784961 696247 (by norm_num) (by norm_num)
      (by norm_num) htype

/-- The ordered Type-I escape at `j=6`, checked as an exact rational identity. -/
theorem least_shift_ten_explicit_ordered_fractions :
    1 ≤ 696247 ∧ 696247 < 71817878050 ∧
    71817878050 < 2247303252494450 ∧
    (4 / 2784961 : ℚ) =
      1 / 696247 + 1 / 71817878050 + 1 / 2247303252494450 := by
  norm_num

private theorem earlier_shift_1_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 1) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 1 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 1 : ℕ) = 2 * (1392481) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 1392481).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h <;> subst r <;> norm_num

private theorem earlier_shift_2_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 2) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 2 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 2 : ℕ) = 3 * (19 * (48859)) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 19).primeFactors, (by norm_num : Nat.Prime 48859).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_3_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 3) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 3 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 3 : ℕ) = 2 ^ 2 * (7 ^ 2 * (13 * (1093))) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 2 (by norm_num : (2 : ℕ) ≠ 0), Nat.primeFactors_pow 7 (by norm_num : (2 : ℕ) ≠ 0), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 7).primeFactors, (by norm_num : Nat.Prime 13).primeFactors, (by norm_num : Nat.Prime 1093).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_4_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 4) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 4 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 4 : ℕ) = 5 * (293 * (1901)) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 5).primeFactors, (by norm_num : Nat.Prime 293).primeFactors, (by norm_num : Nat.Prime 1901).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_5_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 5) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 5 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 5 : ℕ) = 2 * (3 * (41 * (11321))) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 41).primeFactors, (by norm_num : Nat.Prime 11321).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_6_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 6) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 6 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 6 : ℕ) = 97 * (28711) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 97).primeFactors, (by norm_num : Nat.Prime 28711).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h <;> subst r <;> norm_num

private theorem earlier_shift_7_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 7) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 7 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 7 : ℕ) = 2 ^ 3 * (337 * (1033)) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 2 (by norm_num : (3 : ℕ) ≠ 0), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 337).primeFactors, (by norm_num : Nat.Prime 1033).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_8_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 8) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 8 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 8 : ℕ) = 3 ^ 3 * (11 * (9377)) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow 3 (by norm_num : (3 : ℕ) ≠ 0), (by norm_num : Nat.Prime 3).primeFactors, (by norm_num : Nat.Prime 11).primeFactors, (by norm_num : Nat.Prime 9377).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> subst r <;> norm_num

private theorem earlier_shift_9_factors_residue (r : ℕ)
    (hr : r.Prime) (hdiv : r ∣ 2784961 + 9) :
    jacobiSym (r : ℤ) 2784961 = 1 := by
  have hmem : r ∈ (2784961 + 9 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hdiv, by norm_num⟩
  have hf : (2784961 + 9 : ℕ) = 2 * (5 * (278497)) := by norm_num
  rw [hf, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_mul (by norm_num) (by norm_num), (by norm_num : Nat.Prime 2).primeFactors, (by norm_num : Nat.Prime 5).primeFactors, (by norm_num : Nat.Prime 278497).primeFactors] at hmem
  simp only [Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> subst r <;> norm_num

/-- Every earlier shifted prime factor is a residue, but p+10 contains two nonresidues. -/
theorem first_nonresidue_factor_shift_ten :
    (∀ u : ℕ, 0 < u → u < 10 → ∀ r : ℕ, r.Prime → r ∣ 2784961 + u →
      jacobiSym (r : ℤ) 2784961 = 1) ∧
    (191).Prime ∧ (2083).Prime ∧ 191 ∣ 2784961 + 10 ∧ 2083 ∣ 2784961 + 10 ∧
    jacobiSym (191 : ℤ) 2784961 = -1 ∧ jacobiSym (2083 : ℤ) 2784961 = -1 := by
  constructor
  · intro u hu hu10 r hr hdiv
    interval_cases u
    · exact earlier_shift_1_factors_residue r hr hdiv
    · exact earlier_shift_2_factors_residue r hr hdiv
    · exact earlier_shift_3_factors_residue r hr hdiv
    · exact earlier_shift_4_factors_residue r hr hdiv
    · exact earlier_shift_5_factors_residue r hr hdiv
    · exact earlier_shift_6_factors_residue r hr hdiv
    · exact earlier_shift_7_factors_residue r hr hdiv
    · exact earlier_shift_8_factors_residue r hr hdiv
    · exact earlier_shift_9_factors_residue r hr hdiv
  · norm_num

/-- A single certified counterexample to the *concrete intermediate* that the
least shift with a nonresidue factor must give a full Type-II modular witness
using some divisor of that shifted number. The prime remains soluble. -/
theorem least_shift_does_not_force_shifted_typeII :
    (2784961).Prime ∧ 2784961 % 24 = 1 ∧
    (∀ u : ℕ, 0 < u → u < 10 → ∀ r : ℕ, r.Prime → r ∣ 2784961 + u →
      jacobiSym (r : ℤ) 2784961 = 1) ∧
    (191).Prime ∧ 191 ∣ 2784961 + 10 ∧
    jacobiSym (191 : ℤ) 2784961 = -1 ∧
    (¬ ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ d ∣ m ^ 2 ∧ 4 * d < 2784961 ∧
       4 * m - 1 ∣ 2784961 + 10 ∧ 4 * m - 1 ∣ 2784961 + 4 * d) ∧
    Good 2784961 := by
  obtain ⟨hprev, h191, _, hdiv191, _, hneg191, _⟩ :=
    first_nonresidue_factor_shift_ten
  obtain ⟨hpp, hp24, _, _, hgood⟩ := first_six_fibers_fail_and_escape
  exact ⟨hpp, hp24, hprev, h191, hdiv191, hneg191,
    shift_ten_no_full_typeII_factor, hgood⟩

theorem least_quadratic_nonresidue_2784961 :
    jacobiSym (37 : ℤ) 2784961 = -1 ∧
    ∀ n : ℕ, 0 < n → n < 37 → jacobiSym (n : ℤ) 2784961 = 1 := by
  constructor
  · norm_num
  · intro n hn hnlt
    interval_cases n <;> norm_num at *

theorem square_modulus_never_has_negative_jacobi (s r : ℕ) :
    jacobiSym (r : ℤ) (s ^ 2) ≠ -1 := by
  rw [jacobiSym.pow_right]
  rcases jacobiSym.trichotomy (r : ℤ) s with h | h | h <;>
    rw [h] <;> norm_num

theorem square_25_has_no_shift_factor_but_is_good :
    (∀ u r : ℕ, r.Prime → r ∣ 25 + u → jacobiSym (r : ℤ) 25 ≠ -1) ∧
    Good 25 := by
  constructor
  · intro u r _ _
    exact square_modulus_never_has_negative_jacobi 5 r
  · exact square_25_good

end Erdos242
