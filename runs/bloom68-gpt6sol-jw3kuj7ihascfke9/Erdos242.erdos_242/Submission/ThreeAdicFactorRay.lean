import Submission.FirstDenominatorNorm
import Submission.TypeIIOffsetBound

/-!
# A pointwise obstruction to 3-adic shifted-factor rays

This file verifies a complete, finite *subfamily* failure at the hard prime 241.
It neither proves nor disproves the ordered Erdős–Straus conjecture; in fact,
241 has both a full Type-I and a full Type-II witness at x=62.
`Submission.Spec` is not imported or modified.
-/

namespace Erdos242

/-- The automatic `3 (mod 4)` cofactor for every 3-adically shifted
number, and its relation to the first-denominator square divisor. These
identities *alone* do not imply that the offset divides the square. -/
theorem forced_three_cofactor_identity (k t : ℕ) :
    24 * k + 1 + 4 * (3 * t + 2) =
        3 * (4 * (2 * k + t + 1) - 1) ∧
      6 * k + 1 + (3 * t + 2) = 3 * (2 * k + t + 1) := by
  constructor <;> omega

/-- Even allowing *every* `d ≡ 2 (mod 3)` below `p/4` and *every*
`d ∣ m²`, no factor `4m-1` of `241+4d` gives a Type-II certificate.
The factor bound `m≤40` is proved rather than assumed. -/
theorem three_adic_offsets_all_miss_at_241 (m d : ℕ)
    (hm : 0 < m) (hd : 0 < d) (hd3 : d % 3 = 2)
    (hdsq : d ∣ m ^ 2) (hsmall : 4 * d < 241) :
    ¬ (4 * m - 1 ∣ 241 + 4 * d) := by
  intro hdiv
  have hmle : m ≤ 40 := by
    have hb := full_square_axis_bound 241 m d (by norm_num) hm hsmall hdiv
    norm_num at hb
    exact hb
  have hdle : d ≤ 60 := by omega
  have hfinite :
      ∀ m ∈ Finset.range 41, ∀ d ∈ Finset.range 61,
        (0 < m ∧ 0 < d ∧ d % 3 = 2 ∧ d ∣ m ^ 2 ∧ 4 * d < 241) →
          ¬ (4 * m - 1 ∣ 241 + 4 * d) := by decide
  exact hfinite m (Finset.mem_range.mpr (by omega))
    d (Finset.mem_range.mpr (by omega)) ⟨hm, hd, hd3, hdsq, hsmall⟩ hdiv

/-- Both *full* types fail at all eligible pure odd-power-of-three quotient
fibers `a=3^s` of 241: only `a=3` and `a=27` lie below 241. -/
theorem pure_three_power_fibers_miss_at_241 :
    (¬TypeI 241 61 ∧ ¬TypeII 241 61) ∧
      (¬TypeI 241 67 ∧ ¬TypeII 241 67) := by

  have hsplit61 : ∀ r : ℕ, r.Prime → r ∣ 61 → r % 3 = 1 := by
    intro r hr hrd
    have hreq : r = 61 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 61)).mp hrd
    subst r
    norm_num
  have hsplit67 : ∀ r : ℕ, r.Prime → r ∣ 67 → r % 3 = 1 := by
    intro r hr hrd
    have hreq : r = 67 :=
      (Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 67)).mp hrd
    subst r
    norm_num
  have h61 : ¬TypeI 241 61 ∧ ¬TypeII 241 61 := by
    simpa only [show 24 * 10 + 1 = 241 by norm_num,
      show 6 * 10 + 1 = 61 by norm_num] using
      first_denominator_fails_of_split_factors 10 (by simpa using hsplit61)
  have h67 : ¬TypeI 241 67 ∧ ¬TypeII 241 67 := by
    apply no_types_if_divisors_one_mod_three 241 67
    · norm_num
    · norm_num
    · exact split_prime_square_divisors_mod_three 67 hsplit67
  exact ⟨h61, h67⟩

/-- At 241 the *whole* Type-II branch fails at every eligible first
 denominator whose modulus `4x-241` is divisible by three. Such a witness
 would require `d ≡ 2 (mod 3)` and hence contradict the exact modular test
 above. No analogous statement about Type I is claimed here. -/
theorem no_typeII_three_divisible_modulus_at_241 (x : ℕ)
    (hlo : 241 < 4 * x) (hhi : 2 * x < 241)
    (ha3 : 3 ∣ 4 * x - 241) : ¬TypeII 241 x := by
  rintro ⟨d, hd, hdx, hdsq, hadiv⟩
  have hzero : (4 * x - 241) % 3 = 0 := Nat.mod_eq_zero_of_dvd ha3
  have hzero' : (x + d) % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans ha3 hadiv)
  have heq : (4 * x - 241) + 241 = 4 * x := by omega
  have hd3 : d % 3 = 2 := by omega
  have hp : Nat.Prime 241 := by norm_num
  have hsmall : 4 * d < 241 :=
    typeII_offset_lt_quarter 241 x d hp hlo hhi hd hdx hdsq hadiv
  obtain ⟨hm, hdm, _, hdiv, _⟩ :=
    typeII_modular_parameter 241 x d hp hlo hhi hd hdx hdsq hadiv
  exact three_adic_offsets_all_miss_at_241 _ d hm hd hd3 hdm hsmall hdiv

/-- This prime is not a counterexample: the next first denominator has
full Type II with `d=1` and full Type I with `c=124`. -/
theorem three_adic_miss_but_good_241 :
    (241).Prime ∧ 241 % 24 = 1 ∧
      (¬TypeI 241 61 ∧ ¬TypeII 241 61) ∧
      (¬TypeI 241 67 ∧ ¬TypeII 241 67) ∧
      TypeI 241 62 ∧ TypeII 241 62 ∧ Good 241 := by
  have hI : TypeI 241 62 := by
    refine ⟨124, by norm_num, by norm_num, by norm_num⟩
  have hII : TypeII 241 62 := by
    refine ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, pure_three_power_fibers_miss_at_241.1,
    pure_three_power_fibers_miss_at_241.2, hI, hII,
    good_of_typeII 241 62 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hII⟩

end Erdos242
