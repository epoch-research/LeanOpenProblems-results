import Submission.Reductions

/-!
# DEVELOPMENT: a divisor criterion for the prime Erdős–Straus cases

This file develops an exact criterion for the predicate `Erdos242.Development.ES`
(with strictly increasing positive denominators).  It does not assert that the
criterion is always satisfied, and does not prove the Erdős–Straus conjecture.
It neither imports nor modifies `Submission.Spec`.
-/

namespace Erdos242.Development

namespace DivisorCriterion

/-- Clearing denominators, with all four denominators positive. -/
theorem fraction_eq_iff {p x y z : ℕ} (hp : 0 < p) (hx : 0 < x)
    (hy : 0 < y) (hz : 0 < z) :
    (4 / p : ℚ) = 1 / x + 1 / y + 1 / z ↔
      4 * (x * y * z) = p * (y * z + x * z + x * y) := by
  have hp0 : (p : ℚ) ≠ 0 := by positivity
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  have hy0 : (y : ℚ) ≠ 0 := by positivity
  have hz0 : (z : ℚ) ≠ 0 := by positivity
  have hcast :
      (4 * ((x : ℚ) * y * z) = p * (y * z + x * z + x * y)) ↔
      4 * (x * y * z) = p * (y * z + x * z + x * y) := by
    exact_mod_cast Iff.rfl
  rw [← hcast]
  field_simp

/-- The reduced numerator is coprime to `p*x` in the relevant prime range. -/
theorem coprime_q {p x : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hx : 0 < x) (hpx : p < 4 * x) (hxp : x < p) :
    (4 * x - p).Coprime (p * x) := by
  have hp4 : 4 < p := by have := hp.two_le; omega
  have hcp4 : p.Coprime 4 := Nat.coprime_of_lt_prime (by decide) hp4 hp
  have hcpx : p.Coprime x := Nat.coprime_of_lt_prime (by omega) hxp hp
  have hc : p.Coprime (4 * x) := hcp4.mul_right hcpx
  have hqp : (4 * x - p).Coprime p :=
    (Nat.coprime_sub_self_left (Nat.le_of_lt hpx)).mpr hc.symm
  have hqx : (4 * x - p).Coprime x :=
    ((Nat.coprime_self_sub_left (Nat.le_of_lt hpx)).mpr hc).of_dvd_right
      (dvd_mul_left x 4)
  exact hqp.mul_right hqx

/-- The two positive factors reconstruct a strictly ordered representation when `q < p`.
The divisibility witnesses are the quotients `(p*u+a)/q` and `(p*u+b)/q`. -/
theorem es_of_factors {p u q a b : ℕ} (hp : 0 < p) (hu : 0 < u)
    (hq : 0 < q) (hrel : q + p = 4 * u) (hqp : q < p)
    (hab : a < b) (hprod : a * b = (p * u) ^ 2)
    (hya : q ∣ p * u + a) (hzb : q ∣ p * u + b) : ES p := by
  let y := (p * u + a) / q
  let z := (p * u + b) / q
  have hy : p * u + a = q * y := (Nat.mul_div_cancel' hya).symm
  have hz : p * u + b = q * z := (Nat.mul_div_cancel' hzb).symm
  have huy : u < y := by
    apply (Nat.mul_lt_mul_left hq).mp
    have := Nat.mul_lt_mul_of_pos_right hqp hu
    nlinarith only [hy, this]
  have hyz : y < z := by
    apply (Nat.mul_lt_mul_left hq).mp
    omega
  have hmul : (q * y) * (q * z) = p * u * (q * y + q * z) := by
    rw [← hy, ← hz]
    nlinarith only [hprod]
  have hcross : q * y * z = p * u * (y + z) := by
    apply Nat.eq_of_mul_eq_mul_left hq
    nlinarith only [hmul]
  refine ⟨u, y, z, hu, huy, hyz, ?_⟩
  apply (fraction_eq_iff hp hu (by omega) (by omega)).mpr
  have := congrArg (fun t : ℕ => t * (y * z)) hrel
  nlinarith only [hcross, this]

/-- Cancellation through a divisor pair. -/
theorem dvd_complement {q u d v c : ℕ} (hqu : q.Coprime u)
    (hpair : d * v = u ^ 2) (hdiv : q ∣ u + c * d) :
    q ∣ c * u + v := by
  have hqd : q.Coprime d :=
    (hqu.pow_right 2).of_dvd_right ⟨v, hpair.symm⟩
  apply hqd.dvd_of_dvd_mul_left
  have h : q ∣ u * (u + c * d) := dvd_mul_of_dvd_right hdiv u
  convert h using 1
  nlinarith only [hpair]

/-- The Type I congruence in its two interchangeable forms. -/
theorem typeI_congruence {p u q d : ℕ} (hrel : q + p = 4 * u)
    (hqu : q.Coprime u) : q ∣ 4 * d + 1 ↔ q ∣ u + p * d := by
  have heq : u * (4 * d + 1) = q * d + (u + p * d) := by
    nlinarith only [congrArg (fun t : ℕ => t * d) hrel]
  constructor
  · intro h
    have hmul : q ∣ u * (4 * d + 1) := dvd_mul_of_dvd_right h u
    rw [heq] at hmul
    exact (Nat.dvd_add_iff_right (dvd_mul_right q d)).mpr hmul
  · intro h
    apply hqu.dvd_of_dvd_mul_left
    rw [heq]
    exact dvd_add (dvd_mul_right q d) h

end DivisorCriterion

/-- Type I constructor, in paired-divisor form. With `q = 4*u-p`, the
denominators are `(u, (p*u+v)/q, (p*u+p²*d)/q)`. -/
theorem es_of_typeI_pair {p u d v : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hpu : p < 4 * u) (hup : 2 * u < p) (hd : 0 < d)
    (hpair : d * v = u ^ 2) (hdiv : (4 * u - p) ∣ 4 * d + 1) : ES p := by
  let q := 4 * u - p
  have hu : 0 < u := by omega
  have hq : 0 < q := by dsimp [q]; omega
  have hrel : q + p = 4 * u := by dsimp [q]; omega
  have hqp : q < p := by omega
  have hcop := DivisorCriterion.coprime_q hp hmod hu hpu (by omega)
  have hqu : q.Coprime u := hcop.coprime_mul_left_right
  have hdiv' : q ∣ u + p * d :=
    (DivisorCriterion.typeI_congruence hrel hqu).mp hdiv
  have hy : q ∣ p * u + v := DivisorCriterion.dvd_complement hqu hpair hdiv'
  have hz : q ∣ p * u + p ^ 2 * d := by
    convert dvd_mul_of_dvd_right hdiv' p using 1
    ring
  apply DivisorCriterion.es_of_factors hp.pos hu hq hrel hqp (a := v) (b := p ^ 2 * d)
  · have hv : v ≤ u ^ 2 := by nlinarith only [hpair, Nat.mul_le_mul_right v hd]
    have hpp : p ^ 2 ≤ p ^ 2 * d := by nlinarith only [Nat.mul_le_mul_left (p ^ 2) hd]
    nlinarith only [hv, hpp, Nat.mul_self_lt_mul_self (show u < p by omega)]
  · calc
      v * (p ^ 2 * d) = p ^ 2 * (d * v) := by ring
      _ = (p * u) ^ 2 := by rw [hpair]; ring
  · exact hy
  · exact hz

/-- Type II constructor, in paired-divisor form. With `q = 4*u-p`, the
denominators are `(u, p*(u+d)/q, p*(u+v)/q)`. -/
theorem es_of_typeII_pair {p u d v : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (hpu : p < 4 * u) (hup : 2 * u < p) (hd : 0 < d)
    (hpair : d * v = u ^ 2) (hdu : d < u)
    (hdiv : (4 * u - p) ∣ u + d) : ES p := by
  let q := 4 * u - p
  have hu : 0 < u := by omega
  have hq : 0 < q := by dsimp [q]; omega
  have hrel : q + p = 4 * u := by dsimp [q]; omega
  have hqp : q < p := by omega
  have hcop := DivisorCriterion.coprime_q hp hmod hu hpu (by omega)
  have hqu : q.Coprime u := hcop.coprime_mul_left_right
  have hdiv' : q ∣ u + v := by
    simpa using DivisorCriterion.dvd_complement (c := 1) hqu hpair (by simpa using hdiv)
  have hdv : d < v := by
    by_contra h
    have hvd : v ≤ d := by omega
    nlinarith only [hpair, Nat.mul_le_mul_left d hvd, Nat.mul_self_lt_mul_self hdu]
  apply DivisorCriterion.es_of_factors hp.pos hu hq hrel hqp
    (a := p * d) (b := p * v)
  · exact Nat.mul_lt_mul_of_pos_left hdv hp.pos
  · calc
      p * d * (p * v) = p ^ 2 * (d * v) := by ring
      _ = (p * u) ^ 2 := by rw [hpair]; ring
  · simpa only [mul_add] using dvd_mul_of_dvd_right hdiv p
  · simpa only [mul_add] using dvd_mul_of_dvd_right hdiv' p

/-- The disjunction in the requested criterion is sufficient. -/
theorem es_of_divisor_criterion {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (h : ∃ u d : ℕ, p < 4 * u ∧ 2 * u < p ∧ 0 < d ∧ d ∣ u ^ 2 ∧
      ((4 * u - p) ∣ (4 * d + 1) ∨ (d < u ∧ (4 * u - p) ∣ (u + d)))) :
    ES p := by
  obtain ⟨u, d, hpu, hup, hd, ⟨v, hv⟩, hI | ⟨hdu, hII⟩⟩ := h
  · exact es_of_typeI_pair hp hmod hpu hup hd hv.symm hI
  · exact es_of_typeII_pair hp hmod hpu hup hd hv.symm hdu hII

namespace DivisorCriterion

/-- The elementary, strict bounds on the smallest denominator before using primality. -/
theorem denominator_bounds {p x y z : ℕ} (hp : 0 < p) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p < 4 * x ∧ 4 * x < 3 * p := by
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hc := (fraction_eq_iff hp hx hy hz).mp heq
  have hyz0 : 0 < y * z := Nat.mul_pos hy hz
  constructor
  · apply (Nat.mul_lt_mul_right hyz0).mp
    have hpos : 0 < p * (x * z + x * y) := by positivity
    nlinarith only [hc, hpos]
  · apply (Nat.mul_lt_mul_right hyz0).mp
    have hxz : x * z < y * z := Nat.mul_lt_mul_of_pos_right hxy hz
    have hxyz : x * y < y * z := by
      simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_right (lt_trans hxy hyz) hy
    have hsum : y * z + x * z + x * y < 3 * (y * z) := by omega
    have := Nat.mul_lt_mul_of_pos_left hsum hp
    nlinarith only [hc, this]

/-- Factoring the cleared two-term remainder gives positive, ordered factors.
Here `a = (4*x-p)*y-p*x` and `b = (4*x-p)*z-p*x`. -/
theorem factors_of_representation {p x y z : ℕ} (hp : 0 < p) (hx : 0 < x)
    (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a < p * x ∧ a * b = (p * x) ^ 2 ∧
      p * x + a = (4 * x - p) * y ∧ p * x + b = (4 * x - p) * z := by
  have hy : 0 < y := by omega
  have hz : 0 < z := by omega
  have hc := (fraction_eq_iff hp hx hy hz).mp heq
  have hpx := (denominator_bounds hp hx hxy hyz heq).1
  let q := 4 * x - p
  have hq : 0 < q := by dsimp [q]; omega
  have hrel : q + p = 4 * x := by dsimp [q]; omega
  have hcross : q * y * z = p * x * (y + z) := by
    have := congrArg (fun t : ℕ => t * (y * z)) hrel
    nlinarith only [hc, this]
  have hqy : p * x < q * y := by
    apply (Nat.mul_lt_mul_right hz).mp
    have hpos : 0 < p * x * y := Nat.mul_pos (Nat.mul_pos hp hx) hy
    nlinarith only [hcross, hpos]
  have hqz : q * y < q * z := Nat.mul_lt_mul_of_pos_left hyz hq
  have hqy2 : q * y < 2 * (p * x) := by
    apply (Nat.mul_lt_mul_right hz).mp
    have := Nat.mul_lt_mul_of_pos_left hyz (Nat.mul_pos hp hx)
    nlinarith only [hcross, this]
  let a := q * y - p * x
  let b := q * z - p * x
  have ha : p * x + a = q * y := by dsimp [a]; omega
  have hb : p * x + b = q * z := by dsimp [b]; omega
  refine ⟨a, b, by dsimp [a]; omega, by omega, by omega, ?_, ha, hb⟩
  have hmul : (q * y) * (q * z) = p * x * (q * y + q * z) := by
    have := congrArg (fun t : ℕ => q * t) hcross
    nlinarith only [this]
  rw [← ha, ← hb] at hmul
  nlinarith only [hmul]

/-- In the prime range, the smaller factor cannot contain `p²`. -/
theorem not_sq_dvd_small_factor {p x a : ℕ} (hp : 0 < p) (hxp : x < p)
    (ha : 0 < a) (hax : a < p * x) : ¬ p ^ 2 ∣ a := by
  have hlt : a < p ^ 2 := lt_trans hax (by
    simpa only [pow_two] using Nat.mul_lt_mul_of_pos_left hxp hp)
  exact fun h => (not_le_of_gt hlt) (Nat.le_of_dvd ha h)

/-- The two possible distributions of the prime in the smaller factor.
The bound on `a` excludes the third possibility `p² ∣ a`. -/
theorem prime_factor_dichotomy {p x a b : ℕ} (hp : p.Prime)
    (hx : 0 < x) (hxp : x < p) (ha : 0 < a) (hax : a < p * x)
    (hprod : a * b = (p * x) ^ 2) :
    ∃ d v : ℕ, 0 < d ∧ d * v = x ^ 2 ∧
      ((a = v ∧ b = p ^ 2 * d) ∨ (d < x ∧ a = p * d ∧ b = p * v)) := by
  by_cases hpa : p ∣ a
  · obtain ⟨d, had⟩ := hpa
    have hd : 0 < d := by nlinarith only [ha, had]
    have hdx : d < x := by
      apply (Nat.mul_lt_mul_left hp.pos).mp
      omega
    have hpd : ¬ p ∣ d := by
      intro h
      apply not_sq_dvd_small_factor hp.pos hxp ha hax
      rw [had, pow_two]
      exact Nat.mul_dvd_mul_left p h
    have hdb : d * b = p * x ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [had] at hprod
      nlinarith only [hprod]
    have hpb : p ∣ b :=
      (hp.dvd_mul.mp (show p ∣ d * b by rw [hdb]; exact dvd_mul_right p _)).resolve_left hpd
    obtain ⟨v, hbv⟩ := hpb
    have hpair : d * v = x ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [hbv] at hdb
      nlinarith only [hdb]
    exact ⟨d, v, hd, hpair, Or.inr ⟨hdx, had, hbv⟩⟩
  · have hac : a.Coprime (p ^ 2) := hp.coprime_pow_of_not_dvd hpa
    have hadvd : a ∣ x ^ 2 := by
      apply hac.dvd_of_dvd_mul_left
      exact ⟨b, by nlinarith only [hprod]⟩
    obtain ⟨d, hxd⟩ := hadvd
    have hd : 0 < d := by nlinarith only [hxd, Nat.pow_pos hx (n := 2)]
    have hb : b = p ^ 2 * d := by
      apply Nat.eq_of_mul_eq_mul_left ha
      calc
        a * b = (p * x) ^ 2 := hprod
        _ = p ^ 2 * x ^ 2 := by ring
        _ = a * (p ^ 2 * d) := by rw [hxd]; ring
    exact ⟨d, a, hd, by nlinarith only [hxd], Or.inl ⟨rfl, hb⟩⟩

/-- Type I forces the stronger bound on the smallest denominator.
Strict ordering rules out the boundary case as well. -/
theorem typeI_bound {p u y q d v : ℕ} (hmod : p % 4 = 1)
    (hu : 0 < u) (hq : 0 < q) (hrel : q + p = 4 * u) (huy : u < y)
    (hd : 0 < d) (hpair : d * v = u ^ 2) (hy : p * u + v = q * y)
    (hdiv : q ∣ 4 * d + 1) : 2 * u < p := by
  by_contra hn
  have hp2u : p < 2 * u := by omega
  have hqbig : 2 * u + 1 ≤ q := by omega
  have hv2u : 2 * u < v := by
    have hqy := Nat.mul_lt_mul_of_pos_left huy hq
    have hqu := Nat.mul_le_mul_right u (show p + 2 ≤ q by omega)
    nlinarith only [hy, hqy, hqu]
  have hdu : 2 * d < u := by
    apply (Nat.mul_lt_mul_left hu).mp
    have := Nat.mul_lt_mul_of_pos_right hv2u hd
    nlinarith only [hpair, this]
  have := Nat.le_of_dvd (show 0 < 4 * d + 1 by omega) hdiv
  omega

/-- Type II forces the same stronger bound, just by the size of the divisible sum. -/
theorem typeII_bound {p u q d : ℕ} (hmod : p % 4 = 1)
    (hrel : q + p = 4 * u) (hdu : d < u) (hdiv : q ∣ u + d) : 2 * u < p := by
  have := Nat.le_of_dvd (show 0 < u + d by omega) hdiv
  omega

end DivisorCriterion

/-- Necessity for each individual strictly ordered representation.  In particular,
its smallest denominator itself satisfies `p/4 < x < p/2`; no replacement of the
representation or choice of a minimal representation is needed. -/
theorem divisor_criterion_of_representation {p x y z : ℕ} (hp : p.Prime)
    (hmod : p % 4 = 1) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p < 4 * x ∧ 2 * x < p ∧ ∃ d : ℕ, 0 < d ∧ d ∣ x ^ 2 ∧
      ((4 * x - p) ∣ (4 * d + 1) ∨ (d < x ∧ (4 * x - p) ∣ (x + d))) := by
  obtain ⟨hpx, hxp3⟩ := DivisorCriterion.denominator_bounds hp.pos hx hxy hyz heq
  have hxp : x < p := by omega
  let q := 4 * x - p
  have hq : 0 < q := by dsimp [q]; omega
  have hrel : q + p = 4 * x := by dsimp [q]; omega
  have hcop := DivisorCriterion.coprime_q hp hmod hx hpx hxp
  have hqp : q.Coprime p := hcop.coprime_mul_right_right
  have hqx : q.Coprime x := hcop.coprime_mul_left_right
  obtain ⟨a, b, ha, hab, hax, hprod, hya, hzb⟩ :=
    DivisorCriterion.factors_of_representation hp.pos hx hxy hyz heq
  obtain ⟨d, v, hd, hpair, hI | hII⟩ :=
    DivisorCriterion.prime_factor_dichotomy hp hx hxp ha hax hprod
  · obtain ⟨hav, hbd⟩ := hI
    have hdiv' : q ∣ x + p * d := by
      apply hqp.dvd_of_dvd_mul_left
      have h : q ∣ p * x + b := ⟨z, hzb⟩
      rw [hbd] at h
      convert h using 1
      ring
    have hdiv : q ∣ 4 * d + 1 :=
      (DivisorCriterion.typeI_congruence hrel hqx).mpr hdiv'
    have hbound : 2 * x < p := DivisorCriterion.typeI_bound hmod hx hq hrel hxy hd
      hpair (by simpa only [hav] using hya) hdiv
    exact ⟨hpx, hbound, d, hd, ⟨v, hpair.symm⟩, Or.inl hdiv⟩
  · obtain ⟨hdx, had, hbv⟩ := hII
    have hdiv : q ∣ x + d := by
      apply hqp.dvd_of_dvd_mul_left
      have h : q ∣ p * x + a := ⟨y, hya⟩
      simpa only [had, mul_add] using h
    have hbound : 2 * x < p := DivisorCriterion.typeII_bound hmod hrel hdx hdiv
    exact ⟨hpx, hbound, d, hd, ⟨v, hpair.symm⟩, Or.inr ⟨hdx, hdiv⟩⟩

/-- The requested divisor condition is necessary. -/
theorem divisor_criterion_of_es {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1)
    (h : ES p) :
    ∃ u d : ℕ, p < 4 * u ∧ 2 * u < p ∧ 0 < d ∧ d ∣ u ^ 2 ∧
      ((4 * u - p) ∣ (4 * d + 1) ∨ (d < u ∧ (4 * u - p) ∣ (u + d))) := by
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := h
  obtain ⟨hpx, hxp, d, hd, hdvd, hdiv⟩ :=
    divisor_criterion_of_representation hp hmod hx hxy hyz heq
  exact ⟨x, d, hpx, hxp, hd, hdvd, hdiv⟩

/-- Exact divisor criterion for primes congruent to `1 mod 4`.
This equivalence does not assert the existence of the divisors on its right-hand side. -/
theorem es_iff_divisor_criterion {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ES p ↔ ∃ u d : ℕ, p < 4 * u ∧ 2 * u < p ∧ 0 < d ∧ d ∣ u ^ 2 ∧
      ((4 * u - p) ∣ (4 * d + 1) ∨ (d < u ∧ (4 * u - p) ∣ (u + d))) :=
  ⟨divisor_criterion_of_es hp hmod, es_of_divisor_criterion hp hmod⟩

end Erdos242.Development
