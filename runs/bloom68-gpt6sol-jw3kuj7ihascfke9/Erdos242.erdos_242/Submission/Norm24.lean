import Submission.FullSquareAxis
import Submission.CoveringGap

/-!
# The `A² + 24 B²` norm and an exact (conditional) factor axis

For `p = A² + 24 B²`, an eligible modular Type-II modulus `h = 4m-1`
which divides `A` satisfies `h ∣ p+4d` precisely when `h ∣ 6B²+d`.
The second divisibility is NOT implied by the norm representation. In
particular, the proposed choice `h=A` fails at two hard primes, even
though both have ordered solutions at different moduli. This file does
not assert existence of norm coordinates for every hard prime, or edit
or import `Spec.lean`.
-/

namespace Erdos242

/-- The coordinate product `A*B` is *always below* the first-denominator
window: `p = A²+24B² > 4AB` whenever `B>0`. -/
theorem norm24_product_below_window (A B : ℕ) (hB : 0 < B) :
    4 * (A * B) < A ^ 2 + 24 * B ^ 2 := by
  have hs : (0 : ℤ) ≤ ((A : ℤ) - 2 * (B : ℤ)) ^ 2 := sq_nonneg _
  have hb : (0 : ℤ) < (B : ℤ) ^ 2 := pow_pos (by exact_mod_cast hB) _
  have hi : 4 * (A : ℤ) * B < (A : ℤ) ^ 2 + 24 * (B : ℤ) ^ 2 := by
    nlinarith only [hs, hb]
  have hn : 4 * A * B < A ^ 2 + 24 * B ^ 2 := by exact_mod_cast hi
  simpa only [mul_assoc] using hn

/-- **Exact** reduction at a factor of `A`. The coprimality of `4m-1` and `4`
is needed in the forward direction: having a norm or a factor of `A` alone
is insufficient to produce the divisor `d ∣ m²`. -/
theorem norm24_factor_modular_iff (A B m d : ℕ) (hm : 0 < m)
    (hfactor : 4 * m - 1 ∣ A) :
    (4 * m - 1 ∣ (A ^ 2 + 24 * B ^ 2) + 4 * d) ↔
      (4 * m - 1 ∣ 6 * B ^ 2 + d) := by
  let h := 4 * m - 1
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hcop4m : h.Coprime (4 * m) := by
    have hc : h.Coprime (h + 1) :=
      (Nat.coprime_self_add_right).mpr (by simp)
    rwa [hh] at hc
  have hcop4 : h.Coprime 4 := hcop4m.of_dvd_right (dvd_mul_right 4 m)
  have hsq : h ∣ A ^ 2 := by
    rw [pow_two]
    exact hfactor.mul_right A
  have heq : (A ^ 2 + 24 * B ^ 2) + 4 * d =
      A ^ 2 + 4 * (6 * B ^ 2 + d) := by ring
  change (h ∣ (A ^ 2 + 24 * B ^ 2) + 4 * d) ↔ (h ∣ 6 * B ^ 2 + d)
  constructor
  · intro hdiv
    have hmul : h ∣ 4 * (6 * B ^ 2 + d) :=
      (Nat.dvd_add_iff_left hsq).mpr (by simpa only [heq, add_comm] using hdiv)
    exact hcop4.dvd_of_dvd_mul_left hmul
  · intro hred
    rw [heq]
    exact dvd_add hsq (hred.mul_left 4)

/-- An *integral ordered* norm-dependent construction, conditional on an
actual square divisor in the **exact** residue class. No primality is needed.
The fractions furnished by `good_of_shifted_offset` have denominators
`x=(pm+d)/(4m-1)`, `pm`, `p*(m*x/d)` in strictly increasing order. -/
theorem norm24_good_of_factor (A B m d : ℕ) (hm : 0 < m)
    (hd : 0 < d) (hfactor : 4 * m - 1 ∣ A)
    (hdsq : d ∣ m ^ 2) (hsmall : 4 * d < A ^ 2 + 24 * B ^ 2)
    (hred : 4 * m - 1 ∣ 6 * B ^ 2 + d) :
    Good (A ^ 2 + 24 * B ^ 2) := by
  exact good_of_shifted_offset _ m d hsmall hm hd hdsq
    ((norm24_factor_modular_iff A B m d hm hfactor).mpr hred)

/-- `97=1²+24*2²`: `A=1` cannot be `4m-1` for any positive `m`.
The norm is nonetheless soluble at the first candidate `x=25`. -/
theorem norm24_stress_97 :
    (97).Prime ∧ 97 = 1 ^ 2 + 24 * 2 ^ 2 ∧
      (∀ m : ℕ, 0 < m → 4 * m - 1 ≠ 1) ∧ Good 97 := by
  have ht : TypeII 97 25 := by
    refine ⟨5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · intro m hm heq
    omega
  · exact good_of_typeII 97 25 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) ht

/-- At `1249=35²+24`, the tempting `h=A=35=4*9-1` needs
`d ≡ -6 ≡ 29 (mod 35)`. No divisor of `9²` meets this congruence.
This excludes precisely this one norm-coordinate modulus, not Type II. -/
theorem norm24_no_A_axis_1249 :
    ∀ d : ℕ, 0 < d → d ∣ 9 ^ 2 → ¬ (35 ∣ 6 * 1 ^ 2 + d) := by
  intro d hd hdsq hdiv
  have hle : d ≤ 81 := by
    have : d ≤ 9 ^ 2 := Nat.le_of_dvd (by norm_num) hdsq
    omega
  obtain ⟨t, ht⟩ := hdiv
  have hcases : d = 29 ∨ d = 64 := by omega
  rcases hcases with h | h <;> subst d <;> norm_num at hdsq

/-- Nevertheless `7∣A=35` *does* yield a different factor-axis witness:
`7 | 6*1²+1`, with `m=2,d=1`. Also `x=315,d=15` works. -/
theorem norm24_stress_1249 :
    (1249).Prime ∧ 1249 = 35 ^ 2 + 24 * 1 ^ 2 ∧ Good 1249 := by
  have hgood : Good (35 ^ 2 + 24 * 1 ^ 2) :=
    norm24_good_of_factor 35 1 2 1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [show 35 ^ 2 + 24 * 1 ^ 2 = 1249 by norm_num] using
    (show (1249).Prime ∧ 1249 = 35 ^ 2 + 24 * 1 ^ 2 ∧ Good (35 ^ 2 + 24 * 1 ^ 2) from
      ⟨by norm_num, by norm_num, hgood⟩)

/-- A second ordered certificate for the same prime uses the first eligible
multiple of `A=35`, namely `x=315`, and the full square divisor `d=15`. -/
theorem norm24_1249_first_multiple : TypeII 1249 315 := by
  refine ⟨15, by norm_num, by norm_num, by norm_num, by norm_num⟩


/-- At `2521=11²+24*10²`, `h=A=11=4*3-1` would require
`d ≡ -6*10² ≡ 5 (mod 11)`, whereas `d∣3²` allows only `1,3,9`. -/
theorem norm24_no_A_axis_2521 :
    ∀ d : ℕ, 0 < d → d ∣ 3 ^ 2 → ¬ (11 ∣ 6 * 10 ^ 2 + d) := by
  intro d hd hdsq hdiv
  have hle : d ≤ 9 := by
    have : d ≤ 3 ^ 2 := Nat.le_of_dvd (by norm_num) hdsq
    omega
  obtain ⟨t, ht⟩ := hdiv
  have heq : d = 5 := by omega
  subst d
  norm_num at hdsq

/-- Since `A=11` is prime, its only possible factor `4m-1` is `11`.
Thus the *entire* restricted norm-factor axis fails at this soluble prime,
not just one arbitrary choice of `m`. -/
theorem norm24_no_factor_axis_2521 :
    ¬ ∃ m d : ℕ, 0 < m ∧ 0 < d ∧ (4 * m - 1 ∣ 11) ∧
        d ∣ m ^ 2 ∧ (4 * m - 1 ∣ 6 * 10 ^ 2 + d) := by
  rintro ⟨m, d, hm, hd, hfac, hdsq, hred⟩
  have hgt : 1 < 4 * m - 1 := by omega
  have hh : 4 * m - 1 = 11 := by
    rcases (by norm_num : Nat.Prime 11).eq_one_or_self_of_dvd _ hfac with h1 | h11
    · omega
    · exact h11
  have hm3 : m = 3 := by omega
  subst m
  exact norm24_no_A_axis_2521 d hd hdsq (by simpa using hred)


/-- The failed norm-coordinate modulus is not a counterexample: a *different*
Type-II modulus and a full square divisor give an ordered decomposition. -/
theorem norm24_stress_2521 :
    (2521).Prime ∧ 2521 = 11 ^ 2 + 24 * 10 ^ 2 ∧ Good 2521 := by
  exact ⟨by norm_num, by norm_num, test_2521_good⟩

end Erdos242
