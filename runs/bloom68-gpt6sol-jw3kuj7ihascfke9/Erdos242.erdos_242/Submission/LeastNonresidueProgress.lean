import Submission.Classification

/-!
# Exact witnesses at the first multiple of a small nonresidue

For a hard prime `p = 24k+1`, the first multiple of `5` or `7` after
`p/4` admits a full Type-I cofactor whenever `p` is a nonresidue modulo
that small prime. The assumptions below are the elementary residue-class
versions of `(5/p) = -1` and `(7/p) = -1` (by reciprocity). An explicit
prime with least nonresidue `13` instead misses both types at its first
multiple, even though `13` is a primitive root of that candidate's
modulus. These are partial and local results only: no all-prime theorem
or counterexample to Erdős–Straus is claimed.
-/
namespace Erdos242

/-- When `p` is `2` or `3` modulo five, the first multiple of five after
`p/4` has modulus `3` or `7`. The divisor `c=5` works in either case. -/
theorem first_five_multiple_typeI (k : ℕ)
    (h5 : (24 * k + 1) % 5 = 2 ∨ (24 * k + 1) % 5 = 3) :
    let p := 24 * k + 1
    let x := 5 * (p / 20 + 1)
    p < 4 * x ∧ 2 * x < p ∧ TypeI p x := by
  let p : ℕ := 24 * k + 1
  let x : ℕ := 5 * (p / 20 + 1)
  have hk : 3 ≤ k := by rcases h5 with h | h <;> omega
  have hlo : p < 4 * x := by dsimp [p, x]; omega
  have hhi : 2 * x < p := by dsimp [p, x]; omega
  have ha : 4 * x - p = 3 ∨ 4 * x - p = 7 := by
    dsimp [p, x]
    rcases h5 with h | h <;> omega
  have hI : TypeI p x := by
    change ∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧ (4 * x - p) ∣ 4 * c + 1
    refine ⟨5, by norm_num, ?_, ?_⟩
    · refine ⟨5 * (p / 20 + 1) ^ 2, ?_⟩
      dsimp [x]
      ring
    · rcases ha with h3 | h7
      · rw [h3]
        norm_num
      · rw [h7]
        norm_num
  exact ⟨hlo, hhi, hI⟩

/-- When `p=24k+1` is prime and `p` is `3`, `5`, or `6` modulo seven,
the first multiple of seven after `p/4` has modulus `11`, `15`, or `23`.
The exact Type-I divisor is constructed in every case. -/
theorem first_seven_multiple_typeI (k : ℕ)
    (hp : (24 * k + 1).Prime)
    (h7 : (24 * k + 1) % 7 = 3 ∨ (24 * k + 1) % 7 = 5 ∨
      (24 * k + 1) % 7 = 6) :
    let p := 24 * k + 1
    let x := 7 * (p / 28 + 1)
    p < 4 * x ∧ 2 * x < p ∧ TypeI p x := by
  let p : ℕ := 24 * k + 1
  let x : ℕ := 7 * (p / 28 + 1)
  have hk : 3 ≤ k := by rcases h7 with h | h | h <;> omega
  have hlo : p < 4 * x := by dsimp [p, x]; omega
  have hhi : 2 * x < p := by dsimp [p, x]; omega
  have hx7 : x % 7 = 0 := by dsimp [x]; omega
  have ha : 4 * x - p = 11 ∨ 4 * x - p = 15 ∨ 4 * x - p = 23 := by
    dsimp [p, x]
    rcases h7 with h | h | h <;> omega
  have hp5 : p % 5 ≠ 0 := by
    intro h
    have hdiv : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    have heq : p = 5 := (hp.dvd_iff_eq (by norm_num : 5 ≠ 1)).mp hdiv
    dsimp [p] at heq
    omega
  have h63 (hmod : 4 * x - p = 11 ∨ 4 * x - p = 23) : 63 ∣ x ^ 2 := by
    have hx3 : x % 3 = 0 := by
      dsimp [p] at hmod
      rcases hmod with h | h <;> omega
    have hx21 : 21 ∣ x := Nat.dvd_of_mod_eq_zero (by omega : x % 21 = 0)
    obtain ⟨t, ht⟩ := hx21
    refine ⟨7 * t ^ 2, ?_⟩
    rw [ht]
    ring
  have hI : TypeI p x := by
    change ∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧ (4 * x - p) ∣ 4 * c + 1
    rcases ha with h11 | h15 | h23
    · refine ⟨63, by norm_num, h63 (Or.inl h11), ?_⟩
      rw [h11]
      norm_num
    · have hx2 : x % 2 = 0 := by dsimp [p] at h15; omega
      have hx14 : 14 ∣ x := Nat.dvd_of_mod_eq_zero (by omega : x % 14 = 0)
      obtain ⟨t, ht⟩ := hx14
      have htpos : 0 < t := by
        have : 0 < x := by omega
        rw [ht] at this
        omega
      have ht3 : t % 3 = 2 := by
        dsimp [p] at h15
        rw [ht] at h15
        omega
      have ht5 : t % 5 ≠ 0 := by
        intro hz
        have h : p % 5 = 0 := by
          dsimp [p] at h15
          rw [ht] at h15
          omega
        exact hp5 h
      have ht15 : t % 15 = 2 ∨ t % 15 = 8 ∨ t % 15 = 11 ∨
          t % 15 = 14 := by omega
      rcases ht15 with h2 | h8 | h11 | h14
      · refine ⟨28 * t, by positivity, ?_, ?_⟩
        · refine ⟨7 * t, ?_⟩
          rw [ht]
          ring
        · rw [h15]
          omega
      · refine ⟨7 * t, by positivity, ?_, ?_⟩
        · refine ⟨28 * t, ?_⟩
          rw [ht]
          ring
        · rw [h15]
          omega
      · refine ⟨t, htpos, ?_, ?_⟩
        · refine ⟨196 * t, ?_⟩
          rw [ht]
          ring
        · rw [h15]
          omega
      · refine ⟨4 * t, by positivity, ?_, ?_⟩
        · refine ⟨49 * t, ?_⟩
          rw [ht]
          ring
        · rw [h15]
          omega
    · refine ⟨63, by norm_num, h63 (Or.inr h23), ?_⟩
      rw [h23]
      norm_num
  exact ⟨hlo, hhi, hI⟩


/-- The bounded exponent box at `x=13533=3·13·347` misses `8` modulo
`11`, even though it contains 27 divisors and `13` is a primitive root
modulo `11`. Unlike enumerating all integers up to `x²`, this proof
factors any proposed divisor into three prime-power divisors. -/
private theorem no_eight_divisor_13533 (c : ℕ) (hc : c ∣ 13533 ^ 2) :
    c % 11 ≠ 8 := by
  have hfactor : 13533 ^ 2 = 3 ^ 2 * (13 ^ 2 * 347 ^ 2) := by norm_num
  rw [hfactor] at hc
  obtain ⟨u, v, hu, hv, huv⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  obtain ⟨s, t, hs, ht, hst⟩ := exists_dvd_and_dvd_of_dvd_mul hv
  obtain ⟨i, hi, hui⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hu
  obtain ⟨j, hj, hsj⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 13)).mp hs
  obtain ⟨l, hl, htl⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 347)).mp ht
  have hcform : c = 3 ^ i * (13 ^ j * 347 ^ l) := by
    rw [huv, hst, hui, hsj, htl]
  rw [hcform]
  interval_cases i <;> interval_cases j <;> interval_cases l <;> norm_num

/-- The least positive quadratic nonresidue of the hard prime `54121` is
`13`. This checks every smaller positive integer, not only primes. -/
theorem least_quadratic_nonresidue_54121 :
    jacobiSym (13 : ℤ) 54121 = -1 ∧
      ∀ n : ℕ, 0 < n → n < 13 → jacobiSym (n : ℤ) 54121 = 1 := by
  constructor
  · norm_num
  · intro n hn hnlt
    interval_cases n <;> norm_num at *

/-- The least nonresidue is also a primitive root of the *other* modulus
`11` at the failed first denominator. -/
theorem thirteen_primitive_mod_eleven : orderOf (13 : ZMod 11) = 10 := by
  apply (orderOf_eq_iff (x := (13 : ZMod 11)) (by norm_num : 0 < 10)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

/-- `13533` really is the first eligible multiple of `13` after `p/4`,
and its candidate modulus is `11`. -/
theorem first_thirteen_multiple_54121_data :
    13 * (54121 / 52 + 1) = 13533 ∧
      54121 < 4 * 13533 ∧ 2 * 13533 < 54121 ∧
        4 * 13533 - 54121 = 11 := by norm_num


/-- The first multiple of the least nonresidue `13` at the *prime*
`p=54121` misses both full divisor targets. This only excludes the
single first denominator `x=13533`: at `x=13532` the prime has a
Type-I certificate with `c=68`. -/
theorem no_types_54121_at_first_thirteen_multiple :
    Nat.Prime 54121 ∧ 54121 % 24 = 1 ∧
      ¬TypeI 54121 13533 ∧ ¬TypeII 54121 13533 := by
  have ha : 4 * 13533 - 54121 = 11 := by norm_num
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rintro ⟨c, _, hcdvd, hac⟩
    rw [ha] at hac
    have hres : c % 11 = 8 := by
      have hm := Nat.mod_eq_zero_of_dvd hac
      omega
    exact no_eight_divisor_13533 c hcdvd hres
  · rintro ⟨d, _, _, hddvd, hadiv⟩
    rw [ha] at hadiv
    have hres : d % 11 = 8 := by
      have hm := Nat.mod_eq_zero_of_dvd hadiv
      omega
    exact no_eight_divisor_13533 d hddvd hres

/-- The same prime succeeds at a different eligible first denominator. -/
theorem good_54121_at_13532 : Good 54121 := by
  apply good_of_typeI 54121 13532 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨68, by norm_num, ?_, ?_⟩ <;> norm_num


end Erdos242
