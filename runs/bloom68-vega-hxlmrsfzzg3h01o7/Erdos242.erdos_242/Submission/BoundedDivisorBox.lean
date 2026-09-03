import Submission.DivisorCriterion

/-!
# Bounded-divisor-box development

The general result below transports an individual *allowed monomial*
across rows. It is not a generated-subgroup argument. This file also
checks an ES witness for the capacity-gate obstruction p=5410441.
The full finite gate obstruction is independently audited in Python;
Kneser's theorem and its stabilizer refinements are proved on paper in
`BoundedDivisorBox/lemmas.md`, not asserted as new axioms here.
No Spec file is imported or modified.
-/

namespace Erdos242.Development.BoundedDivisorBox

/-- An unbounded cross-row Type I test using the monomials `a` and `1/a`.
The divisibility `4*a | p+q` makes both monomials lie in the actual box. -/
theorem es_of_monomial_divisor {p a q : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (ha : 0 < a) (hq : 0 < q) (hqp : q < p) (hcoord : 4 * a ∣ p + q)
    (ht : q ∣ p * a + 1 ∨ q ∣ p + a) : ES p := by
  obtain ⟨b, hb⟩ := hcoord
  have hbpos : 0 < b := by
    by_contra h
    have : b = 0 := by omega
    simp [this] at hb
    omega
  let u := a * b
  have hu : 0 < u := Nat.mul_pos ha hbpos
  have hrel : q + p = 4 * u := by dsimp [u]; nlinarith only [hb]
  have hpu : p < 4 * u := by omega
  have hup : 2 * u < p := by omega
  have hqeq : 4 * u - p = q := by omega
  have hcop := DivisorCriterion.coprime_q hp hmod hu hpu (by omega)
  have hqa : q.Coprime a := by
    rw [hqeq] at hcop
    exact hcop.coprime_mul_left_right.of_dvd_right (dvd_mul_right a b)
  rcases ht with ht | ht
  · apply es_of_typeI_pair hp hmod hpu hup (d := a * u) (v := b)
    · exact Nat.mul_pos ha hu
    · dsimp [u]; ring
    · rw [hqeq]
      have hadd : q ∣ (p * a + 1) + q * a :=
        dvd_add ht (dvd_mul_right q a)
      convert hadd using 1
      nlinarith only [congrArg (fun n : ℕ => n * a) hrel]
  · apply es_of_typeI_pair hp hmod hpu hup (d := b) (v := a * u)
    · exact hbpos
    · dsimp [u]; ring
    · rw [hqeq]
      apply hqa.dvd_of_dvd_mul_left
      have hadd : q ∣ p + a + q := dvd_add ht (dvd_refl q)
      convert hadd using 1
      dsimp [u] at hrel
      nlinarith only [hrel]

/-- A divisor of `p+1` congruent to 3 modulo 4 produces a row automatically. -/
theorem es_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hqmod : q % 4 = 3) (hdiv : q ∣ p + 1) : ES p := by
  have hq : 0 < q := by omega
  have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hdiv
  have hqp : q < p := by omega
  apply es_of_monomial_divisor hp hmod (a := 1) (by omega) hq hqp
  · apply Nat.dvd_of_mod_eq_zero
    omega
  · left
    simpa using hdiv

/-- A simultaneous failure forces every divisor of `p+1` to avoid 3 modulo 4. -/
theorem no_three_mod_four_divisor_add_one {p : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 1) (hfail : ¬ ES p) :
    ∀ q : ℕ, q ∣ p + 1 → q % 4 ≠ 3 := by
  intro q hq hqmod
  exact hfail (es_of_dvd_add_one hp hmod hqmod hq)

/-- A 7-mod-8 divisor of a 3-mod-8 number at most `2*p+1` lies below `p`. -/
private theorem seven_divisor_lt {p q N : ℕ} (hp : 1 < p)
    (hNle : N ≤ 2 * p + 1) (hNmod : N % 8 = 3) (hqmod : q % 8 = 7)
    (hdiv : q ∣ N) : q < p := by
  obtain ⟨b, hb⟩ := hdiv
  have hres : (7 * (b % 8)) % 8 = 3 := by
    have ht : N % 8 = (q * b) % 8 := congrArg (fun n : ℕ => n % 8) hb
    rw [hNmod, Nat.mul_mod, hqmod] at ht
    exact ht.symm
  have hb5 : 5 ≤ b := by omega
  have hmul := Nat.mul_le_mul_left q hb5
  nlinarith only [hp, hNle, hb, hmul]

/-- The two all-row tests from the allowed monomials `2` and `1/2`. -/
theorem es_of_seven_mod_eight_divisor {p q : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 1) (hqmod : q % 8 = 7)
    (hdiv : q ∣ p + 2 ∨ q ∣ 2 * p + 1) : ES p := by
  have hp2 := hp.two_le
  have hq : 0 < q := by omega
  have hqp : q < p := by
    rcases hdiv with hdiv | hdiv
    · exact seven_divisor_lt (by omega) (by omega) (by omega) hqmod hdiv
    · exact seven_divisor_lt (by omega) (by omega) (by omega) hqmod hdiv
  apply es_of_monomial_divisor hp (by omega) (a := 2) (by omega) hq hqp
  · apply Nat.dvd_of_mod_eq_zero
    omega
  · rcases hdiv with hdiv | hdiv
    · exact Or.inr hdiv
    · exact Or.inl (by simpa only [Nat.mul_comm] using hdiv)

/-- Complementing a 5-mod-8 factor of a 3-mod-8 number gives a 7-mod-8 divisor. -/
private theorem seven_divisor_of_five_factor {N r : ℕ} (hN : N % 8 = 3)
    (hr : r % 8 = 5) (hdiv : r ∣ N) : ∃ q : ℕ, q ∣ N ∧ q % 8 = 7 := by
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨q, ⟨r, by nlinarith only [hq]⟩, ?_⟩
  have hres : (5 * (q % 8)) % 8 = 3 := by
    have ht : N % 8 = (r * q) % 8 := congrArg (fun n : ℕ => n % 8) hq
    rw [hN, Nat.mul_mod, hr] at ht
    exact ht.symm
  omega

/-- Any 5- or 7-mod-8 factor of either linear form forces a bounded-box hit.
The factor need not be prime. -/
theorem es_of_bad_mod_eight_factor {p r : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 1) (hr : r % 8 = 5 ∨ r % 8 = 7)
    (hdiv : r ∣ p + 2 ∨ r ∣ 2 * p + 1) : ES p := by
  rcases hr with hr | hr
  · rcases hdiv with hdiv | hdiv
    · obtain ⟨q, hq, hqmod⟩ := seven_divisor_of_five_factor (by omega) hr hdiv
      exact es_of_seven_mod_eight_divisor hp hmod hqmod (Or.inl hq)
    · obtain ⟨q, hq, hqmod⟩ := seven_divisor_of_five_factor (by omega) hr hdiv
      exact es_of_seven_mod_eight_divisor hp hmod hqmod (Or.inr hq)
  · exact es_of_seven_mod_eight_divisor hp hmod hr hdiv

/-- A genuine cross-row inverse certificate on prime factors of two linear forms. -/
theorem prime_factor_mod_eight_of_failure {p r : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 1) (hfail : ¬ ES p) (hr : r.Prime)
    (hdiv : r ∣ p + 2 ∨ r ∣ 2 * p + 1) : r % 8 = 1 ∨ r % 8 = 3 := by
  have hrne : r ≠ 2 := by
    intro heq
    subst r
    rcases hdiv with hdiv | hdiv
    · have := Nat.mod_eq_zero_of_dvd hdiv
      omega
    · have := Nat.mod_eq_zero_of_dvd hdiv
      omega
  have hodd := hr.mod_two_eq_one_iff_ne_two.mpr hrne
  have hbad : ¬ (r % 8 = 5 ∨ r % 8 = 7) := by
    intro hb
    exact hfail (es_of_bad_mod_eight_factor hp hmod hb hdiv)
  omega

/-- The all-row monomial `3` test. Its divisors are not bounded by a fixed modulus. -/
theorem es_of_eleven_mod_twelve_divisor {p q : ℕ} (hp : p.Prime)
    (hmod : p % 24 = 1) (hqmod : q % 12 = 11)
    (hdiv : q ∣ (3 * p + 1) / 4) : ES p := by
  have hp2 := hp.two_le
  have hNpos : 0 < (3 * p + 1) / 4 := by omega
  have hqle := Nat.le_of_dvd hNpos hdiv
  have hq : 0 < q := by omega
  have hqp : q < p := by omega
  apply es_of_monomial_divisor hp (by omega) (a := 3) (by omega) hq hqp
  · apply Nat.dvd_of_mod_eq_zero
    omega
  · left
    have heq : 4 * ((3 * p + 1) / 4) = p * 3 + 1 := by omega
    rw [← heq]
    exact dvd_mul_of_dvd_right hdiv 4

/-- The obstructing parameter is a prime in the requested residue class. -/
theorem prime_and_one_mod24_5410441 : Nat.Prime 5410441 ∧ 5410441 % 24 = 1 := by
  norm_num

/-- This is not an ES counterexample: a strictly ordered Type II witness. -/
theorem es_5410441 : ES 5410441 := by
  apply es_of_typeII_pair (u := 1352618) (d := 93284) (v := 19612961)
  all_goals norm_num

/-- The cross-row monomial test also closes the capacity obstruction:
`87 | p+2`, and `8 | p+87`. It uses the allowed monomial `1/2`. -/
theorem es_5410441_by_cross_row : ES 5410441 := by
  apply es_of_monomial_divisor (a := 2) (q := 87)
  all_goals norm_num

end Erdos242.Development.BoundedDivisorBox
