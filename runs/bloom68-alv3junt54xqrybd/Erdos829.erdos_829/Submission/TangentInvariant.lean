import Submission.TangentDefinitions

/-!
# Invariants of the integral tangent transformation

The tangent transformation preserves primitive triples with positive denominator on
`a³ + b³ = 9 w³`. Its integral coordinate size increases strictly, so its orbit
from `(2, 1, 1)` consists of distinct triples. Primitive triples with positive
denominator are also uniquely determined by their rational coordinates.
-/

namespace Erdos829Aux.Tangent

theorem good_seed : Good seed := by
  norm_num [Good, seed, isCoprime_one_right]

/-- Equal numerator coordinates are impossible for a good triple. -/
theorem good_a_ne_b {p : Triple} (hp : Good p) : p.a ≠ p.b := by
  intro hab
  have hc : IsCoprime p.a p.a := by simpa [← hab] using hp.2.1
  have hw : (1 : ℤ) ≤ p.w := by
    have := hp.1
    omega
  have hw3 : (1 : ℤ) ≤ p.w ^ 3 := one_le_pow₀ hw
  have heq := hp.2.2
  rw [← hab] at heq
  rcases Int.isUnit_iff.mp (isCoprime_self.mp hc) with ha | ha
  · rw [ha] at heq
    norm_num at heq
    omega
  · rw [ha] at heq
    norm_num at heq
    omega

/-- The raw tangent denominator never vanishes on a good triple. -/
theorem rawStep_w_ne_zero {p : Triple} (hp : Good p) : (rawStep p).w ≠ 0 := by
  change p.w * (p.a ^ 3 - p.b ^ 3) ≠ 0
  refine mul_ne_zero (ne_of_gt hp.1) ?_
  intro h
  have hcube : p.a ^ 3 = p.b ^ 3 := sub_eq_zero.mp h
  exact good_a_ne_b hp ((show Odd (3 : ℕ) by decide).pow_inj.mp hcube)

private theorem good_factor_coprime_three {p : Triple} (hp : Good p) :
    IsCoprime (p.a ^ 3 + 2 * p.b ^ 3) (3 : ℤ) := by
  apply IsCoprime.symm
  apply Int.prime_three.coprime_iff_not_dvd.mpr
  intro hfactor
  have hsum : (3 : ℤ) ∣ p.a ^ 3 + p.b ^ 3 := by
    rw [hp.2.2]
    exact ⟨3 * p.w ^ 3, by ring⟩
  have hb3 : (3 : ℤ) ∣ p.b ^ 3 := by
    convert dvd_sub hfactor hsum using 1
    ring
  have ha3 : (3 : ℤ) ∣ p.a ^ 3 := by
    convert dvd_sub hsum hb3 using 1
    ring
  have hunit : IsUnit (3 : ℤ) :=
    hp.2.1.isUnit_of_dvd' (Int.prime_three.dvd_of_dvd_pow ha3)
      (Int.prime_three.dvd_of_dvd_pow hb3)
  norm_num [Int.isUnit_iff] at hunit

/-- No common factor has to be removed from the tangent numerators. -/
theorem rawStep_coprime {p : Triple} (hp : Good p) :
    IsCoprime (rawStep p).a (rawStep p).b := by
  have hab := hp.2.1
  have hub : IsCoprime (p.a ^ 3 + 2 * p.b ^ 3) p.b := by
    convert (hab.pow_left : IsCoprime (p.a ^ 3) p.b).add_mul_right_left
      (2 * p.b ^ 2) using 1
    ring
  have hav : IsCoprime p.a (2 * p.a ^ 3 + p.b ^ 3) := by
    convert (hab.pow_right : IsCoprime p.a (p.b ^ 3)).mul_add_right_right
      (2 * p.a ^ 2) using 1
    ring
  have huv : IsCoprime (p.a ^ 3 + 2 * p.b ^ 3) (2 * p.a ^ 3 + p.b ^ 3) := by
    have h : IsCoprime (p.a ^ 3 + 2 * p.b ^ 3) (3 * p.b ^ 3) :=
      (good_factor_coprime_three hp).mul_right hub.pow_right
    have h' : IsCoprime (p.a ^ 3 + 2 * p.b ^ 3)
        (-(2 * p.a ^ 3 + p.b ^ 3) + 2 * (p.a ^ 3 + 2 * p.b ^ 3)) := by
      convert h using 1
      ring
    simpa only [neg_neg] using h'.of_add_mul_right_right.neg_right
  change IsCoprime (p.a * (p.a ^ 3 + 2 * p.b ^ 3))
    (-p.b * (2 * p.a ^ 3 + p.b ^ 3))
  rw [neg_mul]
  exact ((hab.mul_right hav).mul_left (hub.mul_right huv)).neg_right

/-- The cubic equation is a polynomial identity before the sign adjustment. -/
theorem rawStep_equation {p : Triple} (hp : Good p) :
    (rawStep p).a ^ 3 + (rawStep p).b ^ 3 = 9 * (rawStep p).w ^ 3 := by
  change (p.a * (p.a ^ 3 + 2 * p.b ^ 3)) ^ 3 +
    (-p.b * (2 * p.a ^ 3 + p.b ^ 3)) ^ 3 =
    9 * (p.w * (p.a ^ 3 - p.b ^ 3)) ^ 3
  calc
    _ = (p.a ^ 3 + p.b ^ 3) * (p.a ^ 3 - p.b ^ 3) ^ 3 := by ring
    _ = _ := by rw [hp.2.2]; ring

/-- The sign-adjusted tangent transformation preserves good triples. -/
theorem good_step {p : Triple} (hp : Good p) : Good (step p) := by
  have hw := rawStep_w_ne_zero hp
  have hc := rawStep_coprime hp
  have he := rawStep_equation hp
  unfold step
  dsimp only
  split_ifs with h
  · change 0 < -(rawStep p).w ∧
      IsCoprime (-(rawStep p).a) (-(rawStep p).b) ∧
      (-(rawStep p).a) ^ 3 + (-(rawStep p).b) ^ 3 = 9 * (-(rawStep p).w) ^ 3
    refine ⟨by omega, hc.neg_neg, ?_⟩
    nlinarith [he]
  · exact ⟨by omega, hc, he⟩

/-- Casting the integral size gives the maximum of the integer absolute values. -/
theorem size_intCast (p : Triple) : (size p : ℤ) = max |p.a| |p.b| := by
  simp only [size, Nat.cast_max, Int.natCast_natAbs]

/-- A good triple cannot have both numerator coordinates of absolute value at most one. -/
theorem two_le_size {p : Triple} (hp : Good p) : 2 ≤ size p := by
  by_contra h
  have hm : (size p : ℤ) ≤ 1 := by exact_mod_cast (show size p ≤ 1 by omega)
  rw [size_intCast, max_le_iff] at hm
  have ha : p.a ≤ 1 := (le_abs_self _).trans hm.1
  have hb : p.b ≤ 1 := (le_abs_self _).trans hm.2
  have hodd : Odd (3 : ℕ) := by decide
  have ha3 : p.a ^ 3 ≤ 1 := by simpa using hodd.strictMono_pow.monotone ha
  have hb3 : p.b ^ 3 ≤ 1 := by simpa using hodd.strictMono_pow.monotone hb
  have hw : 1 ≤ p.w := by
    have := hp.1
    omega
  have hw3 : 1 ≤ p.w ^ 3 := one_le_pow₀ hw
  have he := hp.2.2
  omega

/-- The sign adjustment leaves the integral size unchanged. -/
theorem size_step_eq_rawStep (p : Triple) : size (step p) = size (rawStep p) := by
  unfold step
  dsimp only
  split_ifs <;> simp [size]

/-- Integral polynomial growth, using that a nonzero integer has magnitude at least one. -/

private theorem growth_nonneg_dominant (a b : ℤ) (ha : 2 ≤ a) (hb : |b| ≤ a) :
    a < max |a * (a ^ 3 + 2 * b ^ 3)| |b * (2 * a ^ 3 + b ^ 3)| := by
  have ha0 : 0 ≤ a := by omega
  have ha1 : 1 ≤ a := by omega
  have ha3 : a < a ^ 3 := lt_self_pow₀ (by omega) (by norm_num)
  rcases le_or_gt 0 b with hb0 | hb0
  · have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb0 _
    have hU : a ^ 3 ≤ a ^ 3 + 2 * b ^ 3 := by omega
    have hU0 : 0 ≤ a ^ 3 + 2 * b ^ 3 := by positivity
    have hmul : a ^ 3 ≤ a * (a ^ 3 + 2 * b ^ 3) :=
      hU.trans (by simpa using mul_le_mul_of_nonneg_right ha1 hU0)
    exact ha3.trans_le (hmul.trans ((le_abs_self _).trans (le_max_left _ _)))
  · have hbm : 1 ≤ -b := by omega
    have hbound : -b ≤ a := by simpa [abs_of_neg hb0] using hb
    have hpow : (-b) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by omega) hbound 3
    have hV : a ^ 3 ≤ 2 * a ^ 3 + b ^ 3 := by nlinarith [hpow]
    have hV0 : 0 ≤ 2 * a ^ 3 + b ^ 3 := (pow_nonneg ha0 3).trans hV
    have hmul : a ^ 3 ≤ (-b) * (2 * a ^ 3 + b ^ 3) :=
      hV.trans (by simpa using mul_le_mul_of_nonneg_right hbm hV0)
    have habs : (-b) * (2 * a ^ 3 + b ^ 3) ≤ |b * (2 * a ^ 3 + b ^ 3)| := by
      rw [neg_mul]
      exact neg_le_abs _
    exact ha3.trans_le (hmul.trans (habs.trans (le_max_right _ _)))

private theorem growth_abs_dominant (a b : ℤ) (ha : 2 ≤ |a|) (hb : |b| ≤ |a|) :
    |a| < max |a * (a ^ 3 + 2 * b ^ 3)| |b * (2 * a ^ 3 + b ^ 3)| := by
  rcases le_or_gt 0 a with ha0 | ha0
  · rw [abs_of_nonneg ha0] at ha hb ⊢
    exact growth_nonneg_dominant a b ha hb
  · rw [abs_of_neg ha0] at ha hb ⊢
    have h := growth_nonneg_dominant (-a) (-b) ha (by simpa only [abs_neg] using hb)
    have hA : (-a) * ((-a) ^ 3 + 2 * (-b) ^ 3) = a * (a ^ 3 + 2 * b ^ 3) := by ring
    have hB : (-b) * (2 * (-a) ^ 3 + (-b) ^ 3) = b * (2 * a ^ 3 + b ^ 3) := by ring
    simpa only [hA, hB] using h

private theorem growth_polynomials (a b : ℤ) (hM : 2 ≤ max |a| |b|) :
    max |a| |b| < max |a * (a ^ 3 + 2 * b ^ 3)| |b * (2 * a ^ 3 + b ^ 3)| := by
  rcases le_total |b| |a| with hb | ha
  · rw [max_eq_left hb] at hM ⊢
    exact growth_abs_dominant a b hM hb
  · rw [max_eq_right ha] at hM ⊢
    have h := growth_abs_dominant b a hM ha
    have hA : b * (b ^ 3 + 2 * a ^ 3) = b * (2 * a ^ 3 + b ^ 3) := by ring
    have hB : a * (2 * b ^ 3 + a ^ 3) = a * (a ^ 3 + 2 * b ^ 3) := by ring
    simpa only [hA, hB, max_comm] using h

/-- The tangent step strictly increases the integral coordinate size. -/
theorem size_step_gt {p : Triple} (hp : Good p) : size p < size (step p) := by
  rw [size_step_eq_rawStep]
  apply (Nat.cast_lt (α := ℤ)).mp
  rw [size_intCast, size_intCast]
  have hM : (2 : ℤ) ≤ max |p.a| |p.b| := by
    rw [← size_intCast]
    exact_mod_cast two_le_size hp
  simpa only [rawStep, neg_mul, abs_neg] using growth_polynomials p.a p.b hM

/-- Every member of the tangent orbit is a primitive solution with positive denominator. -/
theorem good_orbit (k : ℕ) : Good (orbit k) := by
  induction k with
  | zero => exact good_seed
  | succ k hk => exact good_step hk

/-- The integral sizes along the orbit form a strictly increasing sequence. -/
theorem size_orbit_strictMono : StrictMono (fun k => size (orbit k)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact size_step_gt (good_orbit k)

/-- In particular, distinct iteration indices give distinct triples. -/
theorem orbit_injective : Function.Injective orbit := by
  intro k l h
  exact size_orbit_strictMono.injective (congrArg size h)

private theorem denominator_dvd {p q : Triple} (hc : IsCoprime p.a p.b)
    (ha : p.a * q.w = q.a * p.w) (hb : p.b * q.w = q.b * p.w) : p.w ∣ q.w := by
  rcases hc with ⟨r, s, hrs⟩
  refine ⟨r * q.a + s * q.b, ?_⟩
  calc
    q.w = (r * p.a + s * p.b) * q.w := by rw [hrs]; ring
    _ = r * (p.a * q.w) + s * (p.b * q.w) := by ring
    _ = p.w * (r * q.a + s * q.b) := by rw [ha, hb]; ring

/-- Primitive coordinate uniqueness in cross-multiplied form. -/
theorem good_eq_of_cross_mul {p q : Triple} (hp : Good p) (hq : Good q)
    (ha : p.a * q.w = q.a * p.w) (hb : p.b * q.w = q.b * p.w) : p = q := by
  have hw : p.w = q.w := Int.dvd_antisymm hp.1.le hq.1.le
    (denominator_dvd hp.2.1 ha hb) (denominator_dvd hq.2.1 ha.symm hb.symm)
  have hA : p.a = q.a := by
    apply mul_right_cancel₀ (ne_of_gt hq.1)
    simpa only [hw] using ha
  have hB : p.b = q.b := by
    apply mul_right_cancel₀ (ne_of_gt hq.1)
    simpa only [hw] using hb
  cases p
  cases q
  simp_all

/-- Two good triples with the same pair of rational coordinates are equal. -/
theorem good_eq_of_rat_pair_eq {p q : Triple} (hp : Good p) (hq : Good q)
    (h : ((p.a : ℚ) / p.w, (p.b : ℚ) / p.w) =
      ((q.a : ℚ) / q.w, (q.b : ℚ) / q.w)) : p = q := by
  have hpw : (p.w : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hp.1
  have hqw : (q.w : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hq.1
  have ha : p.a * q.w = q.a * p.w := by
    exact_mod_cast (div_eq_div_iff hpw hqw).mp (congrArg Prod.fst h)
  have hb : p.b * q.w = q.b * p.w := by
    exact_mod_cast (div_eq_div_iff hpw hqw).mp (congrArg Prod.snd h)
  exact good_eq_of_cross_mul hp hq ha hb

end Erdos829Aux.Tangent
