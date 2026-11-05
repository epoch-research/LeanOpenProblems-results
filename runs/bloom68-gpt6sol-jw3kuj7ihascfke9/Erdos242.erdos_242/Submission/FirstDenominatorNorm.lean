import Submission.CoveringGap
import Submission.NormShiftDescent
import Submission.EisensteinNormBarrier

/-!
# The norm of the *first denominator*, not of the hard prime

For `p = 24k+1`, its first possible ordered denominator is `q = 6k+1`.
We prove the exact split-prime factor test for this ONE fiber, and record
where a representation `q = u²+3v²` does and does not furnish square divisors.
Neither a norm representation nor a quadratic-character sign solves the
universal pointwise Type-I/Type-II covering problem. `Spec.lean` is untouched.
-/

namespace Erdos242

/-- If every prime dividing `q` is `1 (mod 3)`, then so is **every**
positive divisor of `q²`. In particular this does not replace `c∣x²`
by the smaller condition `c∣x`. -/
theorem split_prime_square_divisors_mod_three (q : ℕ)
    (hsplit : ∀ r : ℕ, r.Prime → r ∣ q → r % 3 = 1) :
    ∀ e : ℕ, 0 < e → e ∣ q ^ 2 → e % 3 = 1 := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro he hdiv
    by_cases he1 : e = 1
    · simp [he1]
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd he1
    obtain ⟨t, ht⟩ := hrd
    have htpos : 0 < t := by
      by_contra h
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos h
      rw [ht0] at ht
      simp at ht
      omega
    have htlt : t < e := by
      rw [ht]
      have := hr.two_le
      nlinarith
    have htdvd : t ∣ e := ⟨r, by rw [ht]; ring⟩
    have hrdvd : r ∣ e := ⟨t, ht⟩
    have hrq : r ∣ q := hr.dvd_of_dvd_pow (dvd_trans hrdvd hdiv)
    have htq : t ∣ q ^ 2 := dvd_trans htdvd hdiv
    have hrmod : r % 3 = 1 := hsplit r hr hrq
    have htmod : t % 3 = 1 := ih t htlt htpos htq
    rw [ht]
    simp [Nat.mul_mod, hrmod, htmod]

/-- The full Type-I and Type-II criteria **both** fail at `x₀=q` when
all prime factors of `q` split modulo three. -/
theorem first_denominator_fails_of_split_factors (k : ℕ)
    (hsplit : ∀ r : ℕ, r.Prime → r ∣ 6 * k + 1 → r % 3 = 1) :
    ¬ TypeI (24 * k + 1) (6 * k + 1) ∧
      ¬ TypeII (24 * k + 1) (6 * k + 1) := by
  apply no_types_if_divisors_one_mod_three (24 * k + 1) (6 * k + 1)
  · have : 4 * (6 * k + 1) - (24 * k + 1) = 3 := by omega
    rw [this]
  · omega
  · exact split_prime_square_divisors_mod_three (6 * k + 1) hsplit

/-- An inert prime factor of the first denominator provides an **actual**
Type-I square cofactor, with no primality assumption on `24k+1`. -/
theorem first_denominator_typeI_of_inert_factor (k r : ℕ)
    (hr : r.Prime) (hrq : r ∣ 6 * k + 1) (hr3 : r % 3 = 2) :
    TypeI (24 * k + 1) (6 * k + 1) := by
  have ha : 4 * (6 * k + 1) - (24 * k + 1) = 3 := by omega
  refine ⟨r, hr.pos, ?_, ?_⟩
  · simpa only [pow_two] using hrq.mul_right (6 * k + 1)
  · rw [ha]
    apply Nat.dvd_of_mod_eq_zero
    omega

/-- The *same* factor also supplies Type II: `r<q` because `q=1 mod 3`
but `r=2 mod 3`. In particular the strict order is not being dropped. -/
theorem first_denominator_typeII_of_inert_factor (k r : ℕ)
    (hr : r.Prime) (hrq : r ∣ 6 * k + 1) (hr3 : r % 3 = 2) :
    TypeII (24 * k + 1) (6 * k + 1) := by
  have ha : 4 * (6 * k + 1) - (24 * k + 1) = 3 := by omega
  have hrlt : r < 6 * k + 1 := by
    have hrle : r ≤ 6 * k + 1 := Nat.le_of_dvd (by omega) hrq
    omega
  refine ⟨r, hr.pos, hrlt, ?_, ?_⟩
  · simpa only [pow_two] using hrq.mul_right (6 * k + 1)
  · rw [ha]
    apply Nat.dvd_of_mod_eq_zero
    omega

/-- Exactly the proposed new case split: at the FIRST fiber both full types
work iff `q` has a prime factor `2 mod 3`. Failure of this fiber does **not**
say that `p` is insoluble at another `x`. -/
theorem first_denominator_iff_inert_prime_factor (k : ℕ) :
    (TypeI (24 * k + 1) (6 * k + 1) ∨
      TypeII (24 * k + 1) (6 * k + 1)) ↔
      ∃ r : ℕ, r.Prime ∧ r ∣ 6 * k + 1 ∧ r % 3 = 2 := by
  constructor
  · intro htypes
    by_contra hnone
    have hsplit : ∀ r : ℕ, r.Prime → r ∣ 6 * k + 1 → r % 3 = 1 := by
      intro r hr hrd
      have hnot2 : r % 3 ≠ 2 := by
        intro htwo
        exact hnone ⟨r, hr, hrd, htwo⟩
      have hnot0 : r % 3 ≠ 0 := by
        intro hzero
        have hthree : 3 ∣ 6 * k + 1 :=
          dvd_trans (Nat.dvd_of_mod_eq_zero hzero) hrd
        have hqzero := Nat.mod_eq_zero_of_dvd hthree
        omega
      omega
    obtain ⟨hI, hII⟩ := first_denominator_fails_of_split_factors k hsplit
    exact htypes.elim hI hII
  · rintro ⟨r, hr, hrq, hr3⟩
    exact Or.inl (first_denominator_typeI_of_inert_factor k r hr hrq hr3)

/-- The easy branch of the proposed case split really produces positive,
strictly ordered denominators whenever `24k+1` is prime and `q` has an
inert factor. It is *not* a proof of the complementary split-prime branch. -/
theorem good_of_first_denominator_inert_factor (k r : ℕ)
    (hpp : (24 * k + 1).Prime) (hr : r.Prime)
    (hrq : r ∣ 6 * k + 1) (hr3 : r % 3 = 2) :
    Good (24 * k + 1) := by
  have hk : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hn
    subst k
    norm_num at hpp
  apply (good_iff_hard_indices k hpp).mpr
  refine ⟨0, by omega, ?_⟩
  simpa using Or.inl (first_denominator_typeI_of_inert_factor k r hr hrq hr3)

/-- The alternative, precisely equivalent, statement of the failed-fiber
case: **every prime factor** of `q` must be `1 mod 3`. -/
theorem first_denominator_fails_iff_split_factors (k : ℕ) :
    (¬TypeI (24 * k + 1) (6 * k + 1) ∧
      ¬TypeII (24 * k + 1) (6 * k + 1)) ↔
      ∀ r : ℕ, r.Prime → r ∣ 6 * k + 1 → r % 3 = 1 := by
  constructor
  · intro h r hr hrd
    have hnot0 : r % 3 ≠ 0 := by
      intro hzero
      have hthree : 3 ∣ 6 * k + 1 :=
        dvd_trans (Nat.dvd_of_mod_eq_zero hzero) hrd
      have hqzero := Nat.mod_eq_zero_of_dvd hthree
      omega
    have hnot2 : r % 3 ≠ 2 := by
      intro htwo
      exact h.1 (first_denominator_typeI_of_inert_factor k r hr hrd htwo)
    omega
  · exact first_denominator_fails_of_split_factors k

/-- `q=u²+3v²` is ADDITIVE: when the representation is primitive, its
coordinates are generally *coprime* to `q`, not factors of `q` or `q²`.
The hypothesis `q % 3 = 1` is necessary for coprimality with `u`.
This is a concrete obstruction to simply setting `c=u`, `d=v`, etc.
It does not exclude moving to an entirely different first denominator. -/
theorem primitive_first_norm_coordinates_coprime (u v q : ℕ)
    (huv : u.Coprime v) (hq : q = u ^ 2 + 3 * v ^ 2)
    (hq3 : q % 3 = 1) : u.Coprime q ∧ v.Coprime q := by
  have hu3 : u.Coprime 3 := by
    apply Nat.Coprime.symm
    apply ((by norm_num : Nat.Prime 3).coprime_iff_not_dvd).mpr
    intro hthree
    obtain ⟨w, hw⟩ := hthree
    rw [hq, hw] at hq3
    have hzero : (3 * w) ^ 2 % 3 = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      refine ⟨3 * w ^ 2, ?_⟩
      ring
    have hqzero : ((3 * w) ^ 2 + 3 * v ^ 2) % 3 = 0 := by
      rw [Nat.add_mod, hzero]
      simp
    omega
  have hux : u.Coprime (3 * v ^ 2) := hu3.mul_right (huv.pow_right 2)
  have huvq : v.Coprime (u ^ 2) := (huv.symm.pow_right 2)
  constructor
  · rw [hq, pow_two]
    exact (Nat.coprime_mul_left_add_right u (3 * v ^ 2) u).mpr hux
  · rw [hq]
    have heq : u ^ 2 + 3 * v ^ 2 = u ^ 2 + v * (3 * v) := by ring
    rw [heq]
    exact (Nat.coprime_add_mul_left_right v (u ^ 2) (3 * v)).mpr huvq

/-- Thus neither nontrivial primitive norm coordinate can be used even as a
**full** `c∣q²` or `d∣q²` witness at the first fiber. -/
theorem primitive_first_norm_coordinates_not_square_divisors (u v q : ℕ)
    (huv : u.Coprime v) (hq : q = u ^ 2 + 3 * v ^ 2)
    (hq3 : q % 3 = 1) :
    (1 < u → ¬ u ∣ q ^ 2) ∧ (1 < v → ¬ v ∣ q ^ 2) := by
  obtain ⟨huq, hvq⟩ := primitive_first_norm_coordinates_coprime u v q huv hq hq3
  constructor
  · intro hu hudiv
    have hu1 : u = 1 := (huq.pow_right 2).eq_one_of_dvd hudiv
    omega
  · intro hv hvdiv
    have hv1 : v = 1 := (hvq.pow_right 2).eq_one_of_dvd hvdiv
    omega

/-- The norm representation is NOT equivalent to a failed first fiber:
`q=25=5²+3·0²` has the inert prime factor `5`, and `p=97` works at `q`. -/
theorem first_norm_alone_does_not_imply_failure :
    25 = 5 ^ 2 + 3 * 0 ^ 2 ∧
      TypeI 97 25 ∧ TypeII 97 25 := by
  constructor
  · norm_num
  have hI := first_denominator_typeI_of_inert_factor 4 5
    (by norm_num) (by norm_num) (by norm_num)
  have hII := first_denominator_typeII_of_inert_factor 4 5
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by simpa using hI, by simpa using hII⟩

/-- Exactly what the equation `p=4q-3` says about the Type-II modular
parameter. This is a DIVISIBILITY equivalence, not an existence theorem:
when `3m≤q+d`, a witness requires an *actual* `d∣m²` in the specified
residue class `d≡3m-q (mod 4m-1)` (plus the usual size conditions). -/
theorem first_norm_typeII_modular_iff (q m d : ℕ)
    (hq : 0 < q) (hm : 0 < m) (hbound : 3 * m ≤ q + d) :
    (4 * m - 1 ∣ (4 * q - 3) + 4 * d) ↔
      (4 * m - 1 ∣ q + d - 3 * m) := by
  let h := 4 * m - 1
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hcop4m : h.Coprime (4 * m) := by
    have hc : h.Coprime (h + 1) :=
      (Nat.coprime_self_add_right).mpr (by simp)
    rwa [hh] at hc
  have hcop4 : h.Coprime 4 := hcop4m.of_dvd_right (dvd_mul_right 4 m)
  have heq : (4 * q - 3) + 4 * d =
      4 * (q + d - 3 * m) + h * 3 := by
    dsimp [h]
    omega
  change (h ∣ (4 * q - 3) + 4 * d) ↔ (h ∣ q + d - 3 * m)
  constructor
  · intro hdiv
    have hmul : h ∣ 4 * (q + d - 3 * m) :=
      (Nat.dvd_add_iff_left (dvd_mul_right h 3)).mpr (by
        simpa only [heq, add_comm] using hdiv)
    exact hcop4.dvd_of_dvd_mul_left hmul
  · intro hred
    rw [heq]
    exact dvd_add (hred.mul_left 4) (dvd_mul_right h 3)

/-- The `v`-coordinate gives a possible modular *candidate*, but it still
requires an exact divisor of `v²`: setting `m=v` does not find one. -/
theorem first_norm_v_modular_iff (u v d : ℕ) (hv : 0 < v) :
    (4 * v - 1 ∣ (4 * (u ^ 2 + 3 * v ^ 2) - 3) + 4 * d) ↔
      (4 * v - 1 ∣ u ^ 2 + 3 * v ^ 2 + d - 3 * v) := by
  have hq : 0 < u ^ 2 + 3 * v ^ 2 := by positivity
  have hvpow : v ≤ v ^ 2 := by
    have h := Nat.mul_le_mul_left v (show 1 ≤ v by omega)
    nlinarith
  have hbound : 3 * v ≤ (u ^ 2 + 3 * v ^ 2) + d := by omega
  exact first_norm_typeII_modular_iff (u ^ 2 + 3 * v ^ 2) v d hq hv hbound

/-- The coordinate `v=11` of `619=16²+3·11²` has the **correct negative
Jacobi sign** for a Type-II parameter, but none of `1,11,121`, the divisors
of `v²`, matches its REQUIRED residue `d≡16 (mod 43)`. The prime `2473`
is nevertheless soluble at the unrelated first denominator `620`. -/
theorem first_norm_v_2473_sign_without_exact_divisor :
    jacobiSym (2473 : ℤ) 43 = -1 ∧
      ¬ ∃ d : ℕ, 0 < d ∧ d ∣ 11 ^ 2 ∧ (4 * 11 - 1 ∣ 2473 + 4 * d) := by
  constructor
  · norm_num
  rintro ⟨d, hd, hdsq, hdiv⟩
  have hle : d ≤ 121 := Nat.le_of_dvd (by norm_num) hdsq
  have hmod : d % 43 = 16 := by
    have hz : (2473 + 4 * d) % 43 = 0 :=
      Nat.mod_eq_zero_of_dvd (by simpa using hdiv)
    omega
  have hcases : d = 16 ∨ d = 59 ∨ d = 102 := by omega
  rcases hcases with h | h | h <;> subst d <;> norm_num at hdsq

/-- At `q=16633=85²+3·56²`, **neither norm coordinate** can serve
as a Type-II modular parameter `m` with any `d∣m²`. In particular
`m=v=56` has the necessary NEGATIVE Jacobi sign modulo `223` but
still lacks the exact divisor residue `d≡37 (mod 223)`; imposing the
usual additional `4d<p` cannot repair this. The prime `66529` is
soluble at a later Type-I fiber and via an unrelated Type-II parameter. -/
theorem first_norm_66529_coordinate_parameters_fail :
    jacobiSym (66529 : ℤ) 339 = 1 ∧
    jacobiSym (66529 : ℤ) 223 = -1 ∧
    (¬∃ d : ℕ, 0 < d ∧ d ∣ 85 ^ 2 ∧ (4 * 85 - 1 ∣ 66529 + 4 * d)) ∧
    (¬∃ d : ℕ, 0 < d ∧ d ∣ 56 ^ 2 ∧ (4 * 56 - 1 ∣ 66529 + 4 * d)) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rintro ⟨d, hd, hdsq, hdiv⟩
    have hfactor : 85 ^ 2 = 5 ^ 2 * 17 ^ 2 := by norm_num
    rw [hfactor] at hdsq
    obtain ⟨a, b, ha, hb, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hdsq
    obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp ha
    obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 17)).mp hb
    rw [hab, hai, hbj] at hdiv
    interval_cases i <;> interval_cases j <;> norm_num at hdiv
  · rintro ⟨d, hd, hdsq, hdiv⟩
    have hfactor : 56 ^ 2 = 2 ^ 6 * 7 ^ 2 := by norm_num
    rw [hfactor] at hdsq
    obtain ⟨a, b, ha, hb, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hdsq
    obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp ha
    obtain ⟨j, hj, hbj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hb
    rw [hab, hai, hbj] at hdiv
    interval_cases i <;> interval_cases j <;> norm_num at hdiv

/-- A prime first denominator `6k+1` necessarily fails **both complete
criteria at that fiber**; this says nothing about later denominators. -/
theorem first_denominator_fails_if_prime (k : ℕ)
    (hq : (6 * k + 1).Prime) :
    ¬TypeI (24 * k + 1) (6 * k + 1) ∧
      ¬TypeII (24 * k + 1) (6 * k + 1) := by
  apply first_denominator_fails_of_split_factors
  intro r hr hrd
  have heq : r = 6 * k + 1 := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrd
  rw [heq]
  omega

/-- `193=4·49−3`, `49=1²+3·4²=7²`: the first denominator fails,
but `x=50, c=5` is a genuine full Type-I/ordered solution. -/
theorem first_norm_stress_193 :
    (193).Prime ∧ 49 = 1 ^ 2 + 3 * 4 ^ 2 ∧
      ¬TypeI 193 49 ∧ ¬TypeII 193 49 ∧ TypeI 193 50 ∧ Good 193 := by
  have hfail : ¬TypeI 193 49 ∧ ¬TypeII 193 49 := by
    convert first_denominator_fails_of_split_factors 8 (by
      intro r hr hrd
      have hr7 : r ∣ 7 ^ 2 := by simpa using hrd
      have heq : r = 7 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp
        (hr.dvd_of_dvd_pow hr7)
      rw [heq]) using 1
  have hI : TypeI 193 50 := by
    refine ⟨5, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hI,
    good_of_typeI 193 50 (by norm_num) (by norm_num) (by norm_num) hI⟩

/-- `2521=4·631−3`, `631=22²+3·7²` (prime). At `x=636`, the full
Type-II square divisor is `d=8`, which does NOT divide `x`. -/
theorem first_norm_stress_2521 :
    (2521).Prime ∧ 631 = 22 ^ 2 + 3 * 7 ^ 2 ∧
      ¬TypeI 2521 631 ∧ ¬TypeII 2521 631 ∧ TypeII 2521 636 ∧ Good 2521 := by
  have hfail : ¬TypeI 2521 631 ∧ ¬TypeII 2521 631 := by
    convert first_denominator_fails_if_prime 105 (by norm_num) using 1
  have hII : TypeII 2521 636 := by
    refine ⟨8, by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hII,
    good_of_typeII 2521 636 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hII⟩

/-- `66529=4·16633−3`, `16633=85²+3·56²` (prime). At the first
successful shift `j=4` the Type-I cofactor is `c=2179447 > x=16637`
but really divides `x²`; requiring `c∣x` would miss this witness. -/
theorem first_norm_stress_66529 :
    (66529).Prime ∧ 16633 = 85 ^ 2 + 3 * 56 ^ 2 ∧
      ¬TypeI 66529 16633 ∧ ¬TypeII 66529 16633 ∧
        TypeI 66529 16637 ∧ Good 66529 := by
  have hfail : ¬TypeI 66529 16633 ∧ ¬TypeII 66529 16633 := by
    convert first_denominator_fails_if_prime 2772 (by norm_num) using 1
  have hI : TypeI 66529 16637 := by
    refine ⟨2179447, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hI,
    good_of_typeI 66529 16637 (by norm_num) (by norm_num) (by norm_num) hI⟩

/-- `18481=4·4621−3`, `4621=17²+3·38²` (prime). The first fiber
fails, but both full criteria hold at `x=4625, a=19`. -/
theorem first_norm_stress_18481 :
    (18481).Prime ∧ 4621 = 17 ^ 2 + 3 * 38 ^ 2 ∧
      ¬TypeI 18481 4621 ∧ ¬TypeII 18481 4621 ∧
        TypeI 18481 4625 ∧ TypeII 18481 4625 ∧ Good 18481 := by
  have hfail : ¬TypeI 18481 4621 ∧ ¬TypeII 18481 4621 := by
    convert first_denominator_fails_if_prime 770 (by norm_num) using 1
  have hI : TypeI 18481 4625 := by
    refine ⟨185, by norm_num, by norm_num, by norm_num⟩
  have hII : TypeII 18481 4625 := by
    refine ⟨125, by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hI, hII,
    good_of_typeII 18481 4625 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hII⟩

/-- `2473=4·619−3`, `619=16²+3·11²` (prime). The same `v=11`
whose negative sign fails the Type-II modular test above is harmless:
`x=620, c=5` gives the needed **exact** Type-I divisibility. -/
theorem first_norm_stress_2473 :
    (2473).Prime ∧ 619 = 16 ^ 2 + 3 * 11 ^ 2 ∧
      ¬TypeI 2473 619 ∧ ¬TypeII 2473 619 ∧ TypeI 2473 620 ∧ Good 2473 := by
  have hfail : ¬TypeI 2473 619 ∧ ¬TypeII 2473 619 := by
    convert first_denominator_fails_if_prime 103 (by norm_num) using 1
  have hI : TypeI 2473 620 := by
    refine ⟨5, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hI,
    good_of_typeI 2473 620 (by norm_num) (by norm_num) (by norm_num) hI⟩

/-- `409=4·103−3`, `103=10²+3·1²` (prime). The first fiber fails,
while the next fiber succeeds via the full Type-II divisor `d=1`. -/
theorem first_norm_stress_409 :
    (409).Prime ∧ 103 = 10 ^ 2 + 3 * 1 ^ 2 ∧
      ¬TypeI 409 103 ∧ ¬TypeII 409 103 ∧ TypeII 409 104 ∧ Good 409 := by
  have hfail : ¬TypeI 409 103 ∧ ¬TypeII 409 103 := by
    convert first_denominator_fails_if_prime 17 (by norm_num) using 1
  have hII : TypeII 409 104 := by
    refine ⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, by norm_num, hfail.1, hfail.2, hII,
    good_of_typeII 409 104 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hII⟩

/-- Having reduced to the `q₀`-failed, split-prime branch, **only later
fibers can work**. The remaining existential is precisely the original
pointwise Type-I/II covering obligation, with `j=0` removed. The extra
norm equation `q=u²+3v²` supplies no missing `j`, `c`, or `d`. -/
theorem split_first_denominator_good_iff_later_fiber (k : ℕ)
    (hpp : (24 * k + 1).Prime)
    (hsplit : ∀ r : ℕ, r.Prime → r ∣ 6 * k + 1 → r % 3 = 1) :
    Good (24 * k + 1) ↔ ∃ j : ℕ, 0 < j ∧ j < 6 * k ∧
      (TypeI (24 * k + 1) (6 * k + 1 + j) ∨
       TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  rw [good_iff_hard_indices k hpp]
  constructor
  · rintro ⟨j, hj, hcase⟩
    have hno := first_denominator_fails_of_split_factors k hsplit
    have hjpos : 0 < j := by
      by_contra hn
      have hzero : j = 0 := Nat.eq_zero_of_not_pos hn
      subst j
      have hcase0 : TypeI (24 * k + 1) (6 * k + 1) ∨
          TypeII (24 * k + 1) (6 * k + 1) := by simpa using hcase
      exact hcase0.elim hno.1 hno.2
    exact ⟨j, hjpos, hj, hcase⟩
  · rintro ⟨j, _, hj, hcase⟩
    exact ⟨j, hj, hcase⟩

/-- The **entire** ordered Erdős–Straus assertion is equivalent to
finding a *later* exact square-divisor witness for every prime in the
`q₀`-failed (split-factor) branch. This does not assert this witness
exists; rewriting `q` as `u²+3v²` does not weaken this still-open
pointwise obligation. -/
theorem all_good_iff_split_first_denominator_later_cover :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ k : ℕ, (24 * k + 1).Prime →
        (∀ r : ℕ, r.Prime → r ∣ 6 * k + 1 → r % 3 = 1) →
        ∃ j : ℕ, 0 < j ∧ j < 6 * k ∧
          (TypeI (24 * k + 1) (6 * k + 1 + j) ∨
           TypeII (24 * k + 1) (6 * k + 1 + j)) := by
  constructor
  · intro hall k hpp hsplit
    exact (split_first_denominator_good_iff_later_fiber k hpp hsplit).mp
      (hall _ (by have := hpp.two_le; omega))
  · intro hcover
    apply good_of_hard_primes
    intro p hpp hpmod
    have hpform : p = 24 * (p / 24) + 1 := by omega
    have hprime : (24 * (p / 24) + 1).Prime := by rwa [← hpform]
    by_cases hinert : ∃ r : ℕ, r.Prime ∧ r ∣ 6 * (p / 24) + 1 ∧ r % 3 = 2
    · obtain ⟨r, hr, hrq, hr3⟩ := hinert
      have hg := good_of_first_denominator_inert_factor (p / 24) r
        hprime hr hrq hr3
      rwa [← hpform] at hg
    · have hsplit : ∀ r : ℕ, r.Prime → r ∣ 6 * (p / 24) + 1 →
          r % 3 = 1 := by
        have hno : ¬(TypeI (24 * (p / 24) + 1) (6 * (p / 24) + 1) ∨
            TypeII (24 * (p / 24) + 1) (6 * (p / 24) + 1)) :=
          fun hcase => hinert
            ((first_denominator_iff_inert_prime_factor (p / 24)).mp hcase)
        exact (first_denominator_fails_iff_split_factors (p / 24)).mp
          ⟨fun hI => hno (Or.inl hI), fun hII => hno (Or.inr hII)⟩
      have hg := (split_first_denominator_good_iff_later_fiber
        (p / 24) hprime hsplit).mpr (hcover (p / 24) hprime hsplit)
      rwa [← hpform] at hg

/-! ## A norm-forced first denominator that *cannot* work

The new first-denominator norm yields the identity
`p=(2u)²+3(4v²−1)` with `4v²−1=(2v−1)(2v+1)`. The factors
of the second summand are quadratic residues modulo a hard prime `p`.
Their dyadic multiples can be moved into the eligible interval but still
miss **both full** divisor conditions. This is an obstruction to a canonical
norm-based construction, not an insoluble prime. -/

/-- The elementary factorization behind the *first*-norm obstruction. -/
theorem first_norm_twin_product (v : ℕ) (hv : 0 < v) :
    4 * v ^ 2 - 1 = (2 * v - 1) * (2 * v + 1) := by
  have hleft : (2 * v - 1) + 1 = 2 * v := by omega
  have hmul : (2 * v - 1) * (2 * v + 1) + (2 * v + 1) =
      (2 * v) * (2 * v + 1) := by
    simpa only [add_mul, one_mul] using
      (congrArg (fun w : ℕ => w * (2 * v + 1)) hleft)
  have hvpow : 0 < v ^ 2 := pow_pos hv _
  have htiden : (4 * v ^ 2 - 1) + 1 = 4 * v ^ 2 := by omega
  nlinarith only [hmul, htiden]

/-- An odd prime dividing `(2v−1)(2v+1)` sees
`p≡(2u)² (mod ell)`; quadratic reciprocity gives `(+1)` modulo `p`.
The dyadic prime `2` is handled separately below using `p≡1 (mod 8)`.
The previously proved square-plus-product residue theorem is made public in
`EisensteinNormBarrier.lean` so it can be reused here. -/
theorem first_norm_twin_factor_residue (p u v ell : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hu : 0 < u) (hv : 0 < v)
    (hrep : p + 3 = 4 * (u ^ 2 + 3 * v ^ 2))
    (hell : ell.Prime) (helld : ell ∣ 4 * v ^ 2 - 1) :
    jacobiSym (ell : ℤ) p = 1 := by
  have hvpow : 0 < v ^ 2 := pow_pos hv _
  have ht : 0 < 4 * v ^ 2 - 1 := by omega
  have htiden : (4 * v ^ 2 - 1) + 1 = 4 * v ^ 2 := by omega
  have hprel : p = (2 * u) ^ 2 + 3 * (4 * v ^ 2 - 1) := by
    nlinarith only [hrep, htiden]
  exact square_plus_product_prime_factor_residue p (2 * u) 3 (4 * v ^ 2 - 1)
    ell hpp hp8 (by omega) (by norm_num) ht hprel hell (helld.mul_left 3)

/-- Every dyadic multiple `x=2^e(4v²−1)` lying in the ordered
first-denominator interval fails **both full Type I and Type II**.
This does NOT say other `x` for the same prime fail. -/
theorem first_norm_dyadic_candidate_no_types (p u v e : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1) (hu : 0 < u) (hv : 0 < v)
    (hrep : p + 3 = 4 * (u ^ 2 + 3 * v ^ 2))
    (hlo : p < 4 * (2 ^ e * (4 * v ^ 2 - 1)))
    (hhi : 2 * (2 ^ e * (4 * v ^ 2 - 1)) < p) :
    ¬TypeI p (2 ^ e * (4 * v ^ 2 - 1)) ∧
      ¬TypeII p (2 ^ e * (4 * v ^ 2 - 1)) := by
  apply no_types_if_prime_factors_residue p
    (2 ^ e * (4 * v ^ 2 - 1)) hpp hp8 hlo (by omega)
  intro ell hell helld
  rcases (hell.dvd_mul).mp helld with htwo | htwin
  · have heq : ell = 2 :=
      (Nat.prime_dvd_prime_iff_eq hell (by norm_num : Nat.Prime 2)).mp
        (hell.dvd_of_dvd_pow htwo)
    subst ell
    have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
    change jacobiSym (2 : ℤ) p = 1
    rw [jacobiSym.at_two hpodd, ZMod.χ₈_nat_eq_if_mod_eight]
    have hp2 : p % 2 = 1 := by omega
    simp [hp2, hp8]
  · exact first_norm_twin_factor_residue p u v ell hpp hp8 hu hv hrep hell htwin

/-- An elementary halving argument: if `0<t≤2q−2`, some power of two
places `t` between `q` and `2q−2`. The latter endpoint, not just `<2q`,
matters to obtain the strict `2x<p` ordered bound for `p=4q−3`. -/
theorem dyadic_first_denominator_window (q t : ℕ) (hq : 0 < q)
    (ht : 0 < t) (htop : t ≤ 2 * q - 2) :
    ∃ e : ℕ, q ≤ 2 ^ e * t ∧ 2 ^ e * t ≤ 2 * q - 2 := by
  have hbig : ∃ e : ℕ, q ≤ 2 ^ e * t := by
    refine ⟨q, ?_⟩
    have hpow : q < 2 ^ q := Nat.lt_two_pow_self
    have hmul : 2 ^ q ≤ 2 ^ q * t := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left (2 ^ q) (show 1 ≤ t by omega)
    omega
  let e := Nat.find hbig
  have hlow : q ≤ 2 ^ e * t := Nat.find_spec hbig
  refine ⟨e, hlow, ?_⟩
  by_cases he : e = 0
  · simpa [he] using htop
  · have heprev : e - 1 < e := by omega
    have hmin := Nat.find_min hbig heprev
    have hprev : 2 ^ (e - 1) * t < q := by
      change ¬q ≤ 2 ^ (e - 1) * t at hmin
      omega
    have heq : e = (e - 1) + 1 := by omega
    rw [heq, pow_succ]
    have hmul : 2 ^ (e - 1) * 2 * t = 2 * (2 ^ (e - 1) * t) := by ring
    rw [hmul]
    omega

/-- **Universal but negative** result for the proposed norm branch: every
hard prime *with* a positive `v`-coordinate has a norm-determined eligible
first denominator where neither full Type I nor full Type II can work.
The norm does NOT produce a required exact divisor at a different fiber. -/
theorem first_norm_forces_eligible_failed_fiber (k u v : ℕ)
    (hpp : (24 * k + 1).Prime) (hv : 0 < v)
    (hnorm : 6 * k + 1 = u ^ 2 + 3 * v ^ 2) :
    ∃ e : ℕ, let x := 2 ^ e * (4 * v ^ 2 - 1)
      24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
        ¬TypeI (24 * k + 1) x ∧ ¬TypeII (24 * k + 1) x := by
  have hu : 0 < u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos h
    rw [hu0] at hnorm
    have hthree : 3 ∣ 6 * k + 1 := by
      rw [hnorm]
      simp
    have hzero := Nat.mod_eq_zero_of_dvd hthree
    omega
  have hvpow : 0 < v ^ 2 := pow_pos hv _
  have htpos : 0 < 4 * v ^ 2 - 1 := by omega
  have htiden : (4 * v ^ 2 - 1) + 1 = 4 * v ^ 2 := by omega
  have htop' : (4 * v ^ 2 - 1) + 2 ≤ 2 * (6 * k + 1) := by
    rw [hnorm]
    nlinarith only [htiden, hvpow, Nat.zero_le (u ^ 2)]
  have htop : 4 * v ^ 2 - 1 ≤ 2 * (6 * k + 1) - 2 := by omega
  obtain ⟨e, hlow, hhigh⟩ :=
    dyadic_first_denominator_window (6 * k + 1) (4 * v ^ 2 - 1)
      (by omega) htpos htop
  let x := 2 ^ e * (4 * v ^ 2 - 1)
  have hpx : (24 * k + 1) + 3 = 4 * (6 * k + 1) := by ring
  have hrep : (24 * k + 1) + 3 = 4 * (u ^ 2 + 3 * v ^ 2) := by
    rw [← hnorm]
    ring
  have hlo : 24 * k + 1 < 4 * x := by dsimp [x]; omega
  have hhi : 2 * x < 24 * k + 1 := by dsimp [x]; omega
  have hno := first_norm_dyadic_candidate_no_types (24 * k + 1) u v e
    hpp (by omega) hu hv hrep (by simpa only [x] using hlo)
      (by simpa only [x] using hhi)
  refine ⟨e, ?_⟩
  dsimp
  exact ⟨hlo, hhi, hno.1, hno.2⟩

/-- For the SIX mandated stress tests, this new norm-based dyadic fiber
misses both complete criteria, even though each prime has an ordered
solution at a **different** fiber (`first_norm_stress_*`). -/
theorem first_norm_six_twinned_fibers_fail :
    (¬TypeI 193 63 ∧ ¬TypeII 193 63) ∧
    (¬TypeI 2521 780 ∧ ¬TypeII 2521 780) ∧
    (¬TypeI 66529 25086 ∧ ¬TypeII 66529 25086) ∧
    (¬TypeI 18481 5775 ∧ ¬TypeII 18481 5775) ∧
    (¬TypeI 2473 966 ∧ ¬TypeII 2473 966) ∧
    (¬TypeI 409 192 ∧ ¬TypeII 409 192) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using first_norm_dyadic_candidate_no_types 193 1 4 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simpa using first_norm_dyadic_candidate_no_types 2521 22 7 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simpa using first_norm_dyadic_candidate_no_types 66529 85 56 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simpa using first_norm_dyadic_candidate_no_types 18481 17 38 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simpa using first_norm_dyadic_candidate_no_types 2473 16 11 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · simpa using first_norm_dyadic_candidate_no_types 409 10 1 6
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)




end Erdos242
