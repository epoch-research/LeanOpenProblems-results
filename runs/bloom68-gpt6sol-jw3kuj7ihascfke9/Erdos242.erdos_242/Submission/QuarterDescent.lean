import Submission.Classification

/-!
# A conditional quarter-step on integral Erdős–Straus certificates

When `p = 4q - 3`, an eligible first denominator `s` for the smaller
numerator `q` gives an eligible denominator `4s` for `p`.  The new
first-denominator modulus is `4a+3`, where `a=4s-q`.  Reusing a Type-II
square divisor, or multiplying a Type-I square cofactor by four, gives
an *integral* transfer only with the additional quotient congruences
proved below.  In particular, this is NOT a universal induction on `Good`.
All `Good` instances here have strictly increasing natural denominators.
`Submission.Spec` is not imported or modified.
-/

namespace Erdos242

/-- Exact Euclidean quotient condition for preserving a Type-II divisor
under `q ↦ 4q-3`, `s ↦ 4s`.  The relation `s+d=a*m` is the *source*
certificate; the right side is extra input, not a consequence of it. -/
theorem quarter_typeII_divisibility_iff (s a d m : ℕ)
    (hsource : s + d = a * m) :
    (4 * a + 3 ∣ 4 * s + d) ↔ (4 * a + 3 ∣ 3 * (m + d)) := by
  have hsum : 4 * s + d + 3 * (m + d) = (4 * a + 3) * m := by
    calc
      4 * s + d + 3 * (m + d) = 4 * (s + d) + 3 * m := by ring
      _ = 4 * (a * m) + 3 * m := by rw [hsource]
      _ = (4 * a + 3) * m := by ring
  constructor
  · intro hdiv
    have htotal : 4 * a + 3 ∣ (4 * s + d) + 3 * (m + d) := by
      rw [hsum]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_right hdiv).mpr htotal
  · intro hdiv
    have htotal : 4 * a + 3 ∣ (4 * s + d) + 3 * (m + d) := by
      rw [hsum]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_left hdiv).mpr htotal

/-- Type-II certificate descent on **restricted source data**.  A divisor
`d ∣ s²`, `d<s`, remains a divisor of `(4s)²`, and the quotient condition
above is exactly what ensures `(4a+3) ∣ 4s+d`.  Neither source nor target
primality is used for this certificate-level statement. -/
theorem typeII_quarter_lift (q s a d m : ℕ)
    (hbase : q + a = 4 * s) (ha : 0 < a) (hupper : 2 * s < q)
    (hd : 0 < d) (hds : d < s) (hdsq : d ∣ s ^ 2)
    (hsource : s + d = a * m)
    (hcompat : 4 * a + 3 ∣ 3 * (m + d)) :
    TypeII q s ∧ TypeII (4 * q - 3) (4 * s) := by
  have hsrc : 4 * s - q = a := by omega
  have htgt : 4 * (4 * s) - (4 * q - 3) = 4 * a + 3 := by omega
  have hlarge : d ∣ (4 * s) ^ 2 := by
    obtain ⟨u, hu⟩ := hdsq
    refine ⟨16 * u, ?_⟩
    calc
      (4 * s) ^ 2 = 16 * s ^ 2 := by ring
      _ = 16 * (d * u) := by rw [hu]
      _ = d * (16 * u) := by ring
  constructor
  · refine ⟨d, hd, hds, hdsq, ?_⟩
    rw [hsrc, hsource]
    exact dvd_mul_right a m
  · refine ⟨d, hd, by omega, hlarge, ?_⟩
    rw [htgt]
    exact (quarter_typeII_divisibility_iff s a d m hsource).mpr hcompat

/-- The Type-II lift yields a *strictly ordered* solution whenever the
larger numerator is prime.  Unlike the unrestricted `Good q → Good p`
proposal, this needs the explicit divisor and quotient congruence. -/
theorem good_of_typeII_quarter_lift (q s a d m : ℕ)
    (hbase : q + a = 4 * s) (ha : 0 < a) (hupper : 2 * s < q)
    (hd : 0 < d) (hds : d < s) (hdsq : d ∣ s ^ 2)
    (hsource : s + d = a * m)
    (hcompat : 4 * a + 3 ∣ 3 * (m + d))
    (hp : (4 * q - 3).Prime) : Good (4 * q - 3) := by
  have hII := (typeII_quarter_lift q s a d m hbase ha hupper hd hds
    hdsq hsource hcompat).2
  exact good_of_typeII (4 * q - 3) (4 * s) hp (by have := hp.two_le; omega)
    (by omega) (by omega) hII

/-- Exact Euclidean quotient condition when multiplying a source Type-I
cofactor `c` by four.  It is not implied by `a ∣ 4c+1`. -/
theorem quarter_typeI_divisibility_iff (a c m : ℕ)
    (hsource : 4 * c + 1 = a * m) :
    (4 * a + 3 ∣ 4 * (4 * c) + 1) ↔
      (4 * a + 3 ∣ 3 * (m + 1)) := by
  have hsum : (4 * (4 * c) + 1) + 3 * (m + 1) =
      (4 * a + 3) * m := by
    calc
      (4 * (4 * c) + 1) + 3 * (m + 1) = 4 * (4 * c + 1) + 3 * m := by ring
      _ = 4 * (a * m) + 3 * m := by rw [hsource]
      _ = (4 * a + 3) * m := by ring
  constructor
  · intro hdiv
    have htotal : 4 * a + 3 ∣ (4 * (4 * c) + 1) + 3 * (m + 1) := by
      rw [hsum]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_right hdiv).mpr htotal
  · intro hdiv
    have htotal : 4 * a + 3 ∣ (4 * (4 * c) + 1) + 3 * (m + 1) := by
      rw [hsum]
      exact dvd_mul_right _ _
    exact (Nat.dvd_add_iff_left hdiv).mpr htotal

/-- Type-I certificate descent via `c ↦ 4c`.  This uses the **full**
`c ∣ s²` criterion, not the more restrictive `c ∣ s`.  No primality is
needed, but the additional quotient congruence is indispensable. -/
theorem typeI_quarter_lift (q s a c m : ℕ)
    (hbase : q + a = 4 * s) (ha : 0 < a) (hupper : 2 * s < q)
    (hc : 0 < c) (hcsq : c ∣ s ^ 2)
    (hsource : 4 * c + 1 = a * m)
    (hcompat : 4 * a + 3 ∣ 3 * (m + 1)) :
    TypeI q s ∧ TypeI (4 * q - 3) (4 * s) := by
  have hsrc : 4 * s - q = a := by omega
  have htgt : 4 * (4 * s) - (4 * q - 3) = 4 * a + 3 := by omega
  have hlarge : 4 * c ∣ (4 * s) ^ 2 := by
    obtain ⟨u, hu⟩ := hcsq
    refine ⟨4 * u, ?_⟩
    calc
      (4 * s) ^ 2 = 16 * s ^ 2 := by ring
      _ = 16 * (c * u) := by rw [hu]
      _ = (4 * c) * (4 * u) := by ring
  constructor
  · refine ⟨c, hc, hcsq, ?_⟩
    rw [hsrc, hsource]
    exact dvd_mul_right a m
  · refine ⟨4 * c, by omega, hlarge, ?_⟩
    rw [htgt]
    exact (quarter_typeI_divisibility_iff a c m hsource).mpr hcompat

/-- Both the smaller and larger numerators have **strict** ordered
solutions under the restricted Type-I descent hypotheses. -/
theorem good_of_typeI_quarter_lift (q s a c m : ℕ)
    (hbase : q + a = 4 * s) (ha : 0 < a) (hupper : 2 * s < q)
    (hc : 0 < c) (hcsq : c ∣ s ^ 2)
    (hsource : 4 * c + 1 = a * m)
    (hcompat : 4 * a + 3 ∣ 3 * (m + 1)) :
    Good q ∧ Good (4 * q - 3) := by
  obtain ⟨hI, hI'⟩ := typeI_quarter_lift q s a c m hbase ha hupper
    hc hcsq hsource hcompat
  constructor
  · exact good_of_typeI q s (by omega) (by omega) hupper hI
  · exact good_of_typeI (4 * q - 3) (4 * s) (by omega)
      (by omega) (by omega) hI'

/-- The **restricted** induction input for the quarter-step.  It requires
a Type-I or Type-II square divisor of the *smaller* number and the exact
extra quotient divisibility for the selected preserved divisor.  This is
stronger than `Good q`, even when `q` is prime. -/
def QuarterCompatible (q s : ℕ) : Prop :=
  q < 4 * s ∧ 2 * s < q ∧
    ((∃ c : ℕ, 0 < c ∧ c ∣ s ^ 2 ∧
        4 * s - q ∣ 4 * c + 1 ∧
        4 * (4 * s - q) + 3 ∣ 3 * ((4 * c + 1) / (4 * s - q) + 1)) ∨
     (∃ d : ℕ, 0 < d ∧ d < s ∧ d ∣ s ^ 2 ∧
        4 * s - q ∣ s + d ∧
        4 * (4 * s - q) + 3 ∣ 3 * ((s + d) / (4 * s - q) + d)))

/-- A genuine conditional induction step: a restricted *smaller-input*
certificate produces `Good (4q-3)` with prime target and strict order.
The independent converse/coverage hypothesis is **not** assumed. -/
theorem good_of_quarter_compatible (q s : ℕ)
    (hp : (4 * q - 3).Prime) (hcomp : QuarterCompatible q s) :
    Good (4 * q - 3) := by
  rcases hcomp with ⟨hlo, hhi, htypes⟩
  let a := 4 * s - q
  have hbase : q + a = 4 * s := by dsimp [a]; omega
  have ha : 0 < a := by dsimp [a]; omega
  rcases htypes with ⟨c, hc, hcsq, hdiv, hcompat⟩ |
      ⟨d, hd, hds, hdsq, hdiv, hcompat⟩
  · let m := (4 * c + 1) / a
    have hsource : 4 * c + 1 = a * m := by
      dsimp [a, m]
      exact (Nat.mul_div_cancel' hdiv).symm
    exact (good_of_typeI_quarter_lift q s a c m hbase ha hhi
      hc hcsq hsource hcompat).2
  · let m := (s + d) / a
    have hsource : s + d = a * m := by
      dsimp [a, m]
      exact (Nat.mul_div_cancel' hdiv).symm
    exact good_of_typeII_quarter_lift q s a d m hbase ha hhi hd hds
      hdsq hsource hcompat hp


/-! An alternative predecessor step `q ↦ q+4` keeps the first-denominator
modulus fixed if `s ↦ s+1`.  This tempting integer step cannot keep the
same Type-II divisor or Type-I cofactor when `q≡1 (mod 4)`.  These are
obstructions to **particular** transformations, not to other denominators. -/

/-- A divisor of both squares of consecutive naturals must be one. -/
theorem adjacent_square_common_divisor_eq_one (s e : ℕ)
    (hleft : e ∣ s ^ 2) (hright : e ∣ (s + 1) ^ 2) : e = 1 := by
  have hcop : s.Coprime (s + 1) :=
    (Nat.coprime_self_add_right).mpr (by simp)
  exact Nat.eq_one_of_dvd_coprimes (hcop.pow 2 2) hleft hright

/-- Keeping the same Type-II divisor when translating `q ↦ q+4`,
`s ↦ s+1` would make the unchanged modulus divide two consecutive
integers.  For `q≡1 mod 4` this modulus is `3 mod 4`, not one. -/
theorem no_plus_four_reuse_typeII (q s d : ℕ)
    (hmod : q % 4 = 1) (hlo : q < 4 * s)
    (hsource : 4 * s - q ∣ s + d)
    (htarget : 4 * (s + 1) - (q + 4) ∣ (s + 1) + d) : False := by
  have ha : 4 * (s + 1) - (q + 4) = 4 * s - q := by omega
  have ha_mod : (4 * s - q) % 4 = 3 := by omega
  rw [ha] at htarget
  have htarget' : 4 * s - q ∣ (s + d) + 1 := by
    simpa only [add_assoc, add_comm, add_left_comm] using htarget
  have hdiv1 : 4 * s - q ∣ 1 := (Nat.dvd_add_iff_right hsource).mpr htarget'
  have heq : 4 * s - q = 1 := Nat.dvd_one.mp hdiv1
  omega

/-- The unchanged Type-I cofactor cannot divide both consecutive
first-denominator squares unless it is one; then a `3 mod 4` modulus
would have to divide five, which is impossible. -/
theorem no_plus_four_reuse_typeI (q s c : ℕ)
    (hmod : q % 4 = 1) (hlo : q < 4 * s)
    (hleft : c ∣ s ^ 2) (hright : c ∣ (s + 1) ^ 2)
    (hsource : 4 * s - q ∣ 4 * c + 1) : False := by
  have hc : c = 1 := adjacent_square_common_divisor_eq_one s c hleft hright
  have ha_mod : (4 * s - q) % 4 = 3 := by omega
  have hdiv5 : 4 * s - q ∣ 5 := by simpa only [hc] using hsource
  have hle : 4 * s - q ≤ 5 := Nat.le_of_dvd (by norm_num) hdiv5
  have ha3 : 4 * s - q = 3 := by omega
  have hnot : ¬(3 : ℕ) ∣ 5 := by norm_num
  exact hnot (by rwa [ha3] at hdiv5)


/-- A positive prime-to-prime example outside the `p+4` shifted-divisor
family: `p=5209`, `q=1303`, and `p+4=5213=13·401`, with both factors
`1 mod 4`.  The reused divisor is `d=3`, not the trivial `d=1`. -/
theorem quarter_typeII_5209 :
    (1303).Prime ∧ (5209).Prime ∧
      TypeII 1303 327 ∧ TypeII 5209 1308 ∧
      Good 1303 ∧ Good 5209 := by
  have hcert : TypeII 1303 327 ∧ TypeII 5209 1308 := by
    simpa using typeII_quarter_lift 1303 327 5 3 66
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, hcert.1, hcert.2, ?_, ?_⟩
  · exact good_of_typeII 1303 327 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hcert.1
  · exact good_of_typeII 5209 1308 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hcert.2

/-- A nontrivial hard-prime-to-hard-prime Type-I example: from a full
`c=1300 ∣ 4160²` source cofactor for `q=16633` to the full
`4c=5200 ∣ 16640²` target cofactor for `p=66529`. -/
theorem quarter_typeI_66529 :
    (16633).Prime ∧ (66529).Prime ∧
      TypeI 16633 4160 ∧ TypeI 66529 16640 ∧
      Good 16633 ∧ Good 66529 := by
  have hcert : TypeI 16633 4160 ∧ TypeI 66529 16640 := by
    simpa using typeI_quarter_lift 16633 4160 7 1300 743
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨by norm_num, by norm_num, hcert.1, hcert.2, ?_, ?_⟩
  · exact good_of_typeI 16633 4160 (by norm_num) (by norm_num)
      (by norm_num) hcert.1
  · exact good_of_typeI 66529 16640 (by norm_num) (by norm_num)
      (by norm_num) hcert.2

/-- This example is genuinely in the usual small-modulus residual classes:
`p≡169 mod 840`, `p≡6 mod 11`; neither prime factor of `p+4` is
`3 mod 4`, so the shifted-divisor `d=1` shortcut does not apply. -/
theorem quarter_5209_residual_data :
    5209 % 840 = 169 ∧ 5209 % 11 = 6 ∧
      5209 + 4 = 13 * 401 ∧ (13).Prime ∧ (401).Prime := by
  norm_num

/-- Independently calculate the two Type-II solutions' integral,
strictly increasing denominators and exact rational equalities. -/
theorem quarter_5209_explicit_fractions :
    (327 < 85998 ∧ 85998 < 9373782 ∧
      (4 / 1303 : ℚ) = 1 / 327 + 1 / 85998 + 1 / 9373782) ∧
    (1308 < 296913 ∧ 296913 < 129454068 ∧
      (4 / 5209 : ℚ) = 1 / 1308 + 1 / 296913 + 1 / 129454068) := by
  norm_num

/-- Independently calculate the corresponding integral, ordered
Type-I decompositions in the hard-prime-to-hard-prime example. -/
theorem quarter_66529_explicit_fractions :
    (4160 < 9886656 ∧ 9886656 < 51388984140 ∧
      (4 / 16633 : ℚ) = 1 / 4160 + 1 / 9886656 + 1 / 51388984140) ∧
    (16640 < 35712768 ∧ 35712768 < 742479606960 ∧
      (4 / 66529 : ℚ) = 1 / 16640 + 1 / 35712768 + 1 / 742479606960) := by
  norm_num


/-- All divisors of the **full** square `632²=(2³·79)²` lie in the three
residue classes `1,2,4` modulo seven; neither restricted nor unrestricted
cofactors at this first denominator can have residue five. -/
private theorem quarter_2521_square_divisor_residue (e : ℕ) (he : e ∣ (632 : ℕ) ^ 2) :
    e % 7 = 1 ∨ e % 7 = 2 ∨ e % 7 = 4 := by
  have hfactor : (632 : ℕ) ^ 2 = 2 ^ 6 * 79 ^ 2 := by norm_num
  rw [hfactor] at he
  obtain ⟨u, v, hu, hv, heuv⟩ := exists_dvd_and_dvd_of_dvd_mul he
  obtain ⟨i, hi, hui⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hu
  obtain ⟨j, hj, hvj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 79)).mp hv
  rw [heuv, hui, hvj]
  interval_cases i <;> interval_cases j <;> norm_num

/-- At a genuine eligible first denominator, the naive `s ↦ 4s` transfer
fails **both full certificate types**: `p=2521`, `q=631`, `s=158`,
`4s=632`, `4·632-p=7`.  It says nothing about other first denominators. -/
theorem quarter_2521_no_target_fiber :
    ¬TypeI 2521 632 ∧ ¬TypeII 2521 632 := by
  have ha : 4 * 632 - 2521 = 7 := by norm_num
  constructor
  · rintro ⟨c, _, hc, hdiv⟩
    have hzero : (4 * c + 1) % 7 = 0 :=
      Nat.mod_eq_zero_of_dvd (by simpa only [ha] using hdiv)
    rcases quarter_2521_square_divisor_residue c hc with h | h | h <;> omega
  · rintro ⟨d, _, _, hd, hdiv⟩
    have hzero : (632 + d) % 7 = 0 :=
      Nat.mod_eq_zero_of_dvd (by simpa only [ha] using hdiv)
    rcases quarter_2521_square_divisor_residue d hd with h | h | h <;> omega

/-- Both prime inputs have ordered solutions, and `q=631` has a Type-II
certificate at `s=158`, but there is no solution at its lifted first
denominator `4s=632` for `p=2521`.  This refutes an unconditional
certificate-preserving induction step, **not** the conjecture. -/
theorem quarter_2521_naive_induction_fails :
    (631).Prime ∧ (2521).Prime ∧ TypeII 631 158 ∧
      Good 631 ∧ Good 2521 ∧
      ¬TypeI 2521 632 ∧ ¬TypeII 2521 632 := by
  have hsource : TypeII 631 158 := by
    refine ⟨1, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num
  have hother : TypeII 2521 636 := by
    refine ⟨8, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num
  exact ⟨by norm_num, by norm_num, hsource,
    good_of_typeII 631 158 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsource,
    good_of_typeII 2521 636 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hother,
    quarter_2521_no_target_fiber.1, quarter_2521_no_target_fiber.2⟩

/-- A *finite*, kernel-checked exhaustive obstruction for `q=25`.  An
eligible source first denominator is at most 12; a positive cofactor
`c ∣ s²` is at most 144 and a Type-II divisor `d<s` is at most 11.
The finite decision checks **both** full square-divisor branches with
exact quotient congruences, not a search cutoff for arbitrary primes. -/
private theorem no_quarter_compatible_25_finite :
    ¬ ∃ s : Fin 13, 25 < 4 * s.val ∧ 2 * s.val < 25 ∧
      ((∃ c : Fin 145, 0 < c.val ∧ c.val ∣ s.val ^ 2 ∧
          (4 * s.val - 25) ∣ 4 * c.val + 1 ∧
          (4 * (4 * s.val - 25) + 3) ∣
            3 * ((4 * c.val + 1) / (4 * s.val - 25) + 1)) ∨
       (∃ d : Fin 13, 0 < d.val ∧ d.val < s.val ∧ d.val ∣ s.val ^ 2 ∧
          (4 * s.val - 25) ∣ s.val + d.val ∧
          (4 * (4 * s.val - 25) + 3) ∣
            3 * ((s.val + d.val) / (4 * s.val - 25) + d.val))) := by
  set_option maxRecDepth 10000 in
    decide

/-- The particular *restricted* quarter-step is **not** a universal
prime-induction scheme: none of the eligible source first denominators
for `q=25` satisfies either quotient-compatibility branch. -/
theorem no_quarter_compatible_25 : ¬ ∃ s : ℕ, QuarterCompatible 25 s := by
  rintro ⟨s, hlo, hhi, htypes⟩
  have hs : s < 13 := by omega
  apply no_quarter_compatible_25_finite
  refine ⟨⟨s, hs⟩, hlo, hhi, ?_⟩
  rcases htypes with ⟨c, hc, hcsq, hdiv, hcompat⟩ |
      ⟨d, hd, hds, hdsq, hdiv, hcompat⟩
  · have hspos : 0 < s := by omega
    have hsle : s ≤ 12 := by omega
    have hsqle : s ^ 2 ≤ 12 ^ 2 := Nat.pow_le_pow_left hsle 2
    have hcle : c ≤ s ^ 2 := Nat.le_of_dvd (pow_pos hspos 2) hcsq
    have hcfin : c < 145 := by norm_num at hsqle; omega
    exact Or.inl ⟨⟨c, hcfin⟩, hc, hcsq, hdiv, hcompat⟩
  · have hdfin : d < 13 := by omega
    exact Or.inr ⟨⟨d, hdfin⟩, hd, hds, hdsq, hdiv, hcompat⟩


/-- The only divisors of `7²` are `1,7,49`, all one modulo three. -/
private theorem quarter_25_source_square_divisor (e : ℕ) (he : e ∣ (7 : ℕ) ^ 2) :
    e % 3 = 1 := by
  obtain ⟨j, hj, heq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp he
  rw [heq]
  interval_cases j <;> norm_num

/-- The smaller composite `25` actually has an ordered solution beginning
at `s=7`, but *neither* prime-style source certificate exists there. -/
theorem quarter_25_no_source_fiber : ¬TypeI 25 7 ∧ ¬TypeII 25 7 := by
  have ha : 4 * 7 - 25 = 3 := by norm_num
  constructor
  · rintro ⟨c, _, hcsq, hdiv⟩
    have hc : c % 3 = 1 := quarter_25_source_square_divisor c hcsq
    have hzero : (4 * c + 1) % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (by simpa only [ha] using hdiv)
    omega
  · rintro ⟨d, _, _, hdsq, hdiv⟩
    have hd : d % 3 = 1 := quarter_25_source_square_divisor d hdsq
    have hzero : (7 + d) % 3 = 0 :=
      Nat.mod_eq_zero_of_dvd (by simpa only [ha] using hdiv)
    omega

/-- The **target** `p=97` nevertheless has both types at the lifted
`4s=28`: Type I uses `c=56`, Type II uses `d=2`.  The source certificate
loss is real even though the target first denominator itself works. -/
theorem quarter_97_target_28_both_types : TypeI 97 28 ∧ TypeII 97 28 := by
  constructor
  · refine ⟨56, by norm_num, by norm_num, ?_⟩
    norm_num
  · refine ⟨2, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num

/-- The failure of quarter-compatibility is **not** a counterexample:
`q=25` and the hard prime `p=97=4q-3` both have explicitly ordered
solutions, even though this restricted induction proves neither. -/
theorem quarter_97_good_but_no_lift :
    (97).Prime ∧ 97 % 24 = 1 ∧ Good 25 ∧ Good 97 ∧
      ¬ ∃ s : ℕ, QuarterCompatible 25 s := by
  have hq : Good 25 := by
    refine ⟨7, 60, 2100, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num
  have hp : Good 97 := by
    refine ⟨28, 194, 2716, by norm_num, by norm_num, by norm_num, ?_⟩
    norm_num
  exact ⟨by norm_num, by norm_num, hq, hp, no_quarter_compatible_25⟩



end Erdos242

#print axioms Erdos242.quarter_typeII_divisibility_iff
#print axioms Erdos242.typeII_quarter_lift
#print axioms Erdos242.good_of_typeII_quarter_lift
#print axioms Erdos242.quarter_typeI_divisibility_iff
#print axioms Erdos242.good_of_typeI_quarter_lift
#print axioms Erdos242.quarter_typeII_5209
#print axioms Erdos242.quarter_typeI_66529
#print axioms Erdos242.adjacent_square_common_divisor_eq_one
#print axioms Erdos242.no_plus_four_reuse_typeI
#print axioms Erdos242.no_plus_four_reuse_typeII
#print axioms Erdos242.quarter_5209_explicit_fractions
#print axioms Erdos242.quarter_66529_explicit_fractions
#print axioms Erdos242.quarter_2521_no_target_fiber
#print axioms Erdos242.quarter_2521_naive_induction_fails
#print axioms Erdos242.good_of_quarter_compatible
#print axioms Erdos242.no_quarter_compatible_25
#print axioms Erdos242.quarter_97_good_but_no_lift
#print axioms Erdos242.quarter_25_no_source_fiber
#print axioms Erdos242.quarter_97_target_28_both_types
