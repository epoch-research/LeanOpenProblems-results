import Submission.CoveringGap

/-!
# Pointwise polynomial progressions: exact parameters versus squareclass signs

A modular type-II witness extends to an integral polynomial identity on a
*primitive* progression, already positive at its initial point.  This does not
assert that every nonsquare initial point has such a witness.  The prime 97
and modulus 19 refute the tempting replacement of the exact divisor test by
a quadratic-nonresidue test at a chosen modulus.  `Spec.lean` is not imported.
-/

namespace Erdos242

/-- Any full square-divisor modular witness has a modulus coprime to its
numerator; no primality of the numerator is needed. -/
theorem modular_witness_primitive (n m d : ℕ) (hm : 0 < m)
    (hdsq : d ∣ m ^ 2) (hdiv : 4 * m - 1 ∣ n + 4 * d) :
    Nat.Coprime n (4 * m - 1) := by
  let h := 4 * m - 1
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hcopm : h.Coprime m := by
    apply Nat.coprime_of_dvd
    intro q hq hqh hqm
    have hq4m : q ∣ 4 * m := hqm.mul_left 4
    have hqh1 : q ∣ h + 1 := by rwa [hh]
    have hq1 : q ∣ 1 :=
      (Nat.dvd_add_iff_left hqh).mpr (by simpa only [add_comm] using hqh1)
    exact (ne_of_gt hq.one_lt) (Nat.dvd_one.mp hq1)
  have hcopd : h.Coprime d := hcopm.pow_right 2 |>.of_dvd_right hdsq
  have hcopfour : h.Coprime 4 := by
    apply Nat.coprime_of_dvd
    intro q hq hqh hqfour
    have hq2 : q ∣ 2 := by
      have : q ∣ 2 * 2 := by simpa only [show (4 : ℕ) = 2 * 2 by norm_num] using hqfour
      rcases (hq.dvd_mul).mp this with ht | ht <;> exact ht
    have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2)).mp hq2
    have hodd : h % 2 = 1 := by dsimp [h]; omega
    subst q
    have : h % 2 = 0 := Nat.mod_eq_zero_of_dvd hqh
    omega
  have hcop : h.Coprime (4 * d) := hcopfour.mul_right hcopd
  apply Nat.coprime_of_dvd
  intro q hq hqn hqh
  have hqsum : q ∣ n + 4 * d := dvd_trans hqh hdiv
  have hq4d : q ∣ 4 * d := (Nat.dvd_add_iff_right hqn).mpr hqsum
  have hqcop : q.Coprime (4 * d) := hcop.of_dvd_left hqh
  exact (ne_of_gt hq.one_lt) (hqcop.eq_one_of_dvd hq4d)

/-- A polynomial Type-II identity with *integer coefficients in the progression
parameter*: `N=n+h*t`, `X=x+m*t`, `Y=m*N`, `Z=N*(u+v*t)`.
All three denominators are positive and strictly increasing even at `t=0`.
The hypotheses are just polynomial identities and the initial positivity. -/
private theorem polynomial_typeII_identity (n h m d x u v : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hd : 0 < d) (hxd : d < x)
    (hh : h + 1 = 4 * m) (hx : h * x = n * m + d)
    (hu : d * u = m * x) (hv : d * v = m ^ 2) :
    ∀ t : ℕ, 1 ≤ x + m * t ∧
      x + m * t < m * (n + h * t) ∧
      m * (n + h * t) < (n + h * t) * (u + v * t) ∧
      (4 / (n + h * t) : ℚ) = 1 / (x + m * t) +
        1 / (m * (n + h * t)) + 1 / ((n + h * t) * (u + v * t)) := by
  intro t
  let N := n + h * t
  let X := x + m * t
  let U := u + v * t
  have hN : 0 < N := by dsimp [N]; omega
  have hX : d < X := by dsimp [X]; omega
  have hh3 : 3 ≤ h := by omega
  have hNX : h * X = N * m + d := by
    calc
      h * X = h * x + (h * t) * m := by dsimp [X]; ring
      _ = n * m + d + (h * t) * m := by rw [hx]
      _ = N * m + d := by dsimp [N]; ring
  have hU : d * U = m * X := by
    calc
      d * U = d * u + (d * v) * t := by dsimp [U]; ring
      _ = m * x + m ^ 2 * t := by rw [hu, hv]
      _ = m * X := by dsimp [X]; ring
  have hXY : X < m * N := by
    have hthree : 3 * X ≤ h * X := Nat.mul_le_mul_right X hh3
    rw [hNX, mul_comm N m] at hthree
    omega
  have hmU : m < U := by
    have hlt : d * m < d * U := by
      calc
        d * m = m * d := by ring
        _ < m * X := Nat.mul_lt_mul_of_pos_left hX hm
        _ = d * U := hU.symm
    exact (Nat.mul_lt_mul_left hd).mp hlt
  have hYZ : m * N < N * U := by
    simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_left hmU hN
  have hpoly : 4 * X * m * U = N * m * U + X * U + X * m := by
    calc
      4 * X * m * U = (h + 1) * X * U := by rw [hh]; ring
      _ = (h * X + X) * U := by ring
      _ = (N * m + d + X) * U := by rw [hNX]
      _ = N * m * U + X * U + d * U := by ring
      _ = N * m * U + X * U + X * m := by rw [hU]; ring
  have hXpos : (X : ℚ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  have hNpos : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmpos : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hUpos : (U : ℚ) ≠ 0 := by exact_mod_cast (by omega : U ≠ 0)
  have hfrac : (4 / N : ℚ) = 1 / X + 1 / (m * N) + 1 / (N * U) := by
    field_simp
    have hpolyQ : 4 * (X : ℚ) * m * U = N * m * U + X * U + X * m := by
      exact_mod_cast hpoly
    nlinarith only [hpolyQ]
  exact ⟨by change 1 ≤ X; omega, by simpa only [N, X] using hXY,
    by simpa only [N, U] using hYZ,
    by simpa only [N, X, U, Nat.cast_add, Nat.cast_mul] using hfrac⟩

/-- An actual modular witness produces a pointwise primitive polynomial
progression.  Its initial ordered denominators (at `t=0`) are explicitly
`x, m*n, n*u`; *no* ``sufficiently large t`` caveat is needed.
The exact `d|m²` condition is essential for the coefficient `v=m²/d`. -/
theorem modular_witness_polynomial_progression (n m d : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hd : 0 < d)
    (hdsq : d ∣ m ^ 2) (hdiv : 4 * m - 1 ∣ n + 4 * d)
    (hxd : d < (n * m + d) / (4 * m - 1)) :
    ∃ h x u v : ℕ, h = 4 * m - 1 ∧ Nat.Coprime n h ∧
      h * x = n * m + d ∧ d * u = m * x ∧ d * v = m ^ 2 ∧
      ∀ t : ℕ, 1 ≤ x + m * t ∧
        x + m * t < m * (n + h * t) ∧
        m * (n + h * t) < (n + h * t) * (u + v * t) ∧
        (4 / (n + h * t) : ℚ) = 1 / (x + m * t) +
          1 / (m * (n + h * t)) + 1 / ((n + h * t) * (u + v * t)) := by
  let h := 4 * m - 1
  let a := (n + 4 * d) / h
  let x := (n * m + d) / h
  let u := m * x / d
  let v := m ^ 2 / d
  have hh : 0 < h := by dsimp [h]; omega
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have ha : h * a = n + 4 * d := Nat.mul_div_cancel' hdiv
  have hsum : n * m + d + h * d = h * (m * a) := by
    calc
      n * m + d + h * d = n * m + (h + 1) * d := by ring
      _ = (n + 4 * d) * m := by rw [hfour]; ring
      _ = h * (m * a) := by rw [← ha]; ring
  have hnum : h ∣ n * m + d := by
    have hdivsum : h ∣ n * m + d + h * d := by
      rw [hsum]
      exact dvd_mul_right h _
    exact (Nat.dvd_add_iff_left (dvd_mul_right h d)).mpr hdivsum
  have hx : h * x = n * m + d := Nat.mul_div_cancel' hnum
  have hxa : x + d = m * a := by
    apply Nat.eq_of_mul_eq_mul_left hh
    calc
      h * (x + d) = n * m + d + h * d := by rw [mul_add, hx]
      _ = h * (m * a) := hsum
  have hdmx : d ∣ m * x := by
    have hmult : m * x + m * d = (m * m) * a := by
      calc
        m * x + m * d = m * (x + d) := by ring
        _ = m * (m * a) := by rw [hxa]
        _ = (m * m) * a := by ring
    have hdall : d ∣ m * x + m * d := by
      rw [hmult]
      exact dvd_mul_of_dvd_left (by simpa only [pow_two] using hdsq) a
    exact (Nat.dvd_add_iff_left (Nat.dvd_mul_left d m)).mpr hdall
  have hu : d * u = m * x := Nat.mul_div_cancel' hdmx
  have hv : d * v = m ^ 2 := Nat.mul_div_cancel' hdsq
  exact ⟨h, x, u, v, rfl, modular_witness_primitive n m d hm hdsq hdiv,
    hx, hu, hv, polynomial_typeII_identity n h m d x u v hn hm hd hxd
      hfour hx hu hv⟩

/-- Full Type-I certificates at hard primes persist on a primitive progression.
This keeps the *full* condition `c ∣ x²` (rather than the restricted `c ∣ x`).
The progressions are positive at the original prime, not merely eventually. -/
theorem typeI_primitive_progression (p x c : ℕ) (hp : p.Prime)
    (hp24 : p % 24 = 1) (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hc : 0 < c) (hcx : c ∣ x ^ 2) (hac : 4 * x - p ∣ 4 * c + 1) :
    let a := 4 * x - p
    let Q := 4 * a * c
    Nat.Coprime p Q ∧ ∀ t : ℕ, Good (p + Q * t) := by
  let a := 4 * x - p
  let Q := 4 * a * c
  have ha : 0 < a := by dsimp [a]; omega
  have ha_lt : a < p := by dsimp [a]; omega
  have hx : 0 < x := by omega
  have hx_lt : x < p := by omega
  have hpa : p.Coprime a := (hp.coprime_iff_not_dvd).mpr
    (Nat.not_dvd_of_pos_of_lt ha ha_lt)
  have hp4 : p.Coprime 4 := (hp.coprime_iff_not_dvd).mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) (by
      have := hp.two_le
      omega))
  have hpc : p.Coprime c := (hp.coprime_iff_not_dvd).mpr (by
    intro hpd
    have hpxsq : p ∣ x ^ 2 := dvd_trans hpd hcx
    have hpx : p ∣ x := hp.dvd_of_dvd_pow hpxsq
    exact (Nat.not_dvd_of_pos_of_lt hx hx_lt) hpx)
  have hcop : p.Coprime Q := by
    dsimp [Q]
    exact (hp4.mul_right hpa).mul_right hpc
  refine ⟨hcop, ?_⟩
  intro t
  let N := p + Q * t
  let X := x + a * c * t
  have hax : a + p = 4 * x := by dsimp [a]; omega
  have hXrel : 4 * X = N + a := by
    calc
      4 * X = 4 * x + Q * t := by dsimp [X, Q]; ring
      _ = (p + a) + Q * t := by rw [add_comm p a, hax]
      _ = N + a := by dsimp [N]; omega
  have hNX : N < 4 * X := by omega
  have hXdouble : 2 * X < N := by
    have hrX : 2 * X = 2 * x + 2 * (a * c * t) := by dsimp [X]; ring
    have hrN : N = p + 4 * (a * c * t) := by dsimp [N, Q]; ring
    rw [hrX, hrN]
    omega
  have hcsqX : c ∣ X ^ 2 := by
    have heq : X ^ 2 = x ^ 2 + c * (2 * x * a * t + c * (a * t) ^ 2) := by
      dsimp [X]; ring
    rw [heq]
    exact dvd_add hcx (dvd_mul_right c _)
  have hdiv : 4 * X - N ∣ 4 * c + 1 := by
    have hsub : 4 * X - N = a := by omega
    rw [hsub]
    exact hac
  have hpN : 0 < N := by
    have := hp.two_le
    dsimp [N]
    omega
  exact good_of_typeI N X hpN hNX hXdouble ⟨c, hc, hcsqX, hdiv⟩

/-- At *each already soluble hard prime*, the full Type-I/II classification
produces a primitive progression whose **first member is that prime** and
whose members are all good.  In Type II the denominator polynomials are the
ones in `modular_witness_polynomial_progression`; the Type-I construction
uses `X=x+a*c*t` and the usual explicit quadratic denominators.
This is conditional on `Good p`, not a proof that every hard prime is good. -/
theorem hard_prime_good_primitive_progression (p : ℕ) (hp : p.Prime)
    (hp24 : p % 24 = 1) (hgood : Good p) :
    ∃ Q : ℕ, 0 < Q ∧ Nat.Coprime p Q ∧ ∀ t : ℕ, Good (p + Q * t) := by
  have hgt : 2 < p := by
    have := hp.two_le
    omega
  obtain ⟨x, hlo, hhi, hw⟩ := (good_iff_ordered_divisors p hp hgt).mp hgood
  rcases hw with hI | hII
  · obtain ⟨c, hc, hcx, hac⟩ := hI
    have ha : 0 < 4 * x - p := by omega
    have hprogress := typeI_primitive_progression p x c hp hp24 hlo hhi hc hcx hac
    exact ⟨4 * (4 * x - p) * c, by positivity, hprogress.1, hprogress.2⟩
  · obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
    obtain ⟨hm, hdmsq, hh, hdiv, hx⟩ :=
      typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
    let m := (x + d) / (4 * x - p)
    have hxd' : d < (p * m + d) / (4 * m - 1) := by
      rw [← hx]
      exact hdx
    obtain ⟨h, x', u, v, hheq, hcop, _, _, _, hfam⟩ :=
      modular_witness_polynomial_progression p m d (by omega) hm hd hdmsq hdiv hxd'
    refine ⟨h, by rw [hheq]; exact hh, hcop, ?_⟩
    intro t
    obtain ⟨hX, hXY, hYZ, hfrac⟩ := hfam t
    exact ⟨x' + m * t, m * (p + h * t), (p + h * t) * (u + v * t),
      hX, hXY, hYZ, by simpa only [Nat.cast_add, Nat.cast_mul] using hfrac⟩

/-- If desired the same primitive progression can be kept entirely within
`1 mod 24`: multiply its modulus by `24` and substitute `24*t` in the
already-established identities.  This is still conditional on `Good p`. -/
theorem hard_prime_good_hard_progression (p : ℕ) (hp : p.Prime)
    (hp24 : p % 24 = 1) (hgood : Good p) :
    ∃ Q : ℕ, 0 < Q ∧ 24 ∣ Q ∧ Nat.Coprime p Q ∧
      ∀ t : ℕ, (p + Q * t) % 24 = 1 ∧ Good (p + Q * t) := by
  obtain ⟨Q, hQ, hcop, hfamily⟩ :=
    hard_prime_good_primitive_progression p hp hp24 hgood
  have hpgt : 24 < p := by
    have := hp.two_le
    omega
  have hcop24 : p.Coprime 24 :=
    (hp.coprime_iff_not_dvd).mpr (Nat.not_dvd_of_pos_of_lt (by decide) hpgt)
  refine ⟨24 * Q, by positivity, dvd_mul_right 24 Q,
    hcop24.mul_right hcop, ?_⟩
  intro t
  have hform : p + (24 * Q) * t = p + Q * (24 * t) := by ring
  constructor
  · have hzero : ((24 * Q) * t) % 24 = 0 :=
      Nat.mod_eq_zero_of_dvd ⟨Q * t, by ring⟩
    rw [Nat.add_mod, hp24, hzero]
  · rw [hform]
    exact hfamily (24 * t)

/-- Primality is genuinely needed when the **Type-I** base cofactor is used
to prove the *chosen modulus* `4ac` primitive.  The nonsquare hard composite
`505=5*101` has this Type-I certificate, but its natural modulus is
`4*15*26=1560`, with `gcd(505,1560)=5`.  A different certificate at
`x=129` exists; the example does **not** refute existence of some
primitive progression at 505. -/
theorem composite_typeI_chosen_modulus_not_primitive :
    505 % 24 = 1 ∧ TypeI 505 130 ∧
      ¬ Nat.Coprime 505 (4 * (4 * 130 - 505) * 26) ∧
      TypeI 505 129 ∧ Good 505 := by
  have hI : TypeI 505 130 :=
    ⟨26, by norm_num, by norm_num, by norm_num⟩
  have hI' : TypeI 505 129 :=
    ⟨129, by norm_num, by norm_num, by norm_num⟩
  exact ⟨by norm_num, hI, by norm_num [Nat.Coprime], hI',
    good_of_typeI 505 130 (by norm_num) (by norm_num) (by norm_num) hI⟩





/-- The modulus/divisor congruence alone does not impose the order condition
`d<x`: `(n,m,d)=(97,28,392)` has the same positive fractions but its
canonical middle and last denominators come out in reverse order. -/
theorem modular_divisor_without_order_condition :
    392 ∣ 28 ^ 2 ∧ 4 * 28 - 1 ∣ 97 + 4 * 392 ∧
      (97 * 28 + 392) / (4 * 28 - 1) = 28 ∧
      ¬ (392 < (97 * 28 + 392) / (4 * 28 - 1)) ∧
      (4 / 97 : ℚ) = 1 / 28 + 1 / 2716 + 1 / 194 := by
  norm_num



/-- The three full divisor targets fail at the candidate `x=29` for the hard
prime 97, despite `97` being a quadratic nonresidue modulo `a=19`. -/
theorem nonresidue_mod19_not_a_certificate :
    (97).Prime ∧ 97 % 24 = 1 ∧ (19).Prime ∧ 19 % 4 = 3 ∧
      (∀ r : ℕ, r < 19 → r ^ 2 % 19 ≠ 97 % 19) ∧
      ¬ (∃ d : ℕ, 0 < d ∧ d ∣ 5 ^ 2 ∧ 19 ∣ 97 + 4 * d) ∧
      ¬ TypeI 97 29 ∧ ¬ TypeII 97 29 := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · intro r hr
    interval_cases r <;> norm_num
  constructor
  · intro ⟨d, hd, hdsq, hdiv⟩
    have hd_cases : d = 1 ∨ d = 5 ∨ d = 25 := by
      obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdsq
      interval_cases e <;> norm_num
    rcases hd_cases with rfl | rfl | rfl <;> norm_num at hdiv
  constructor
  · intro ⟨c, hc, hcsq, hdiv⟩
    have hc_cases : c = 1 ∨ c = 29 ∨ c = 841 := by
      obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 29)).mp hcsq
      interval_cases e <;> norm_num
    rcases hc_cases with rfl | rfl | rfl <;> norm_num at hdiv
  · intro ⟨d, hd, hdx, hdsq, hdiv⟩
    have hd_cases : d = 1 ∨ d = 29 ∨ d = 841 := by
      obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 29)).mp hdsq
      interval_cases e <;> norm_num
    rcases hd_cases with rfl | rfl | rfl
    · norm_num at hdiv
    · norm_num at hdx
    · norm_num at hdx


/-- Consequently the *whole ordered fiber* with first denominator 29 is
absent, not just one choice of cofactor.  The same prime is soluble at 28. -/
theorem no_ordered_97_first_29 :
    ¬∃ y z : ℕ, 29 < y ∧ y < z ∧
      (4 / 97 : ℚ) = 1 / 29 + 1 / y + 1 / z := by
  rintro ⟨y, z, hxy, hyz, heq⟩
  obtain ⟨_, _, _, _, _, _, hnoI, hnoII⟩ := nonresidue_mod19_not_a_certificate
  by_cases hpy : 97 ∣ y
  · exact hnoII (typeII_of_ordered 97 29 y z (by norm_num)
      (by norm_num) (by norm_num) hxy hyz heq hpy)
  · exact hnoI (typeI_of_ordered 97 29 y z (by norm_num)
      (by norm_num) (by norm_num) hxy hyz heq hpy)

/-- The same prime *does* have a positive ordered certificate with a different,
primitive, modulus: `(m,d,h)=(2,2,7)`. -/
theorem good_97_from_seven : Good 97 := by
  apply good_of_modular_witness 97 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The prime 97 belongs to the primitive *hard-class* polynomial progression
`N=97+168t` (gcd(97,168)=1), with explicit positive ordered denominators
starting already at `(28,194,2716)` for `t=0`. -/
theorem polynomial_97_hard_progression (t : ℕ) :
    Nat.Coprime 97 168 ∧ 1 ≤ 28 + 48 * t ∧
      28 + 48 * t < 2 * (97 + 168 * t) ∧
      2 * (97 + 168 * t) < (97 + 168 * t) * (28 + 48 * t) ∧
      (4 / (97 + 168 * t) : ℚ) = 1 / (28 + 48 * t) +
        1 / (2 * (97 + 168 * t)) +
        1 / ((97 + 168 * t) * (28 + 48 * t)) := by
  let N := 97 + 168 * t
  let X := 28 + 48 * t
  have hN : 0 < N := by dsimp [N]; omega
  have hX : 2 < X := by dsimp [X]; omega
  have hXY : X < 2 * N := by dsimp [X, N]; omega
  have hYZ : 2 * N < N * X := by
    simpa only [mul_comm N 2] using Nat.mul_lt_mul_of_pos_left hX hN
  have hrel : 7 * X = 2 * N + 2 := by dsimp [X, N]; ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hXq : (X : ℚ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  have hfrac : (4 / N : ℚ) = 1 / X + 1 / (2 * N) + 1 / (N * X) := by
    have hrelQ : 7 * (X : ℚ) = 2 * N + 2 := by exact_mod_cast hrel
    calc
      (4 / N : ℚ) = (8 * X) / (2 * N * X) := by field_simp; ring
      _ = (2 * N + X + 2) / (2 * N * X) := by congr 1; nlinarith only [hrelQ]
      _ = 1 / X + 1 / (2 * N) + 1 / (N * X) := by field_simp
  exact ⟨by decide, by change 1 ≤ X; omega, by simpa only [N, X] using hXY,
    by simpa only [N, X] using hYZ,
    by simpa only [N, X, Nat.cast_add, Nat.cast_mul] using hfrac⟩


/-- A second, independent prime example from **full Type I**, now with all
three denominator polynomials displayed (the modulus is `4*7*5=140`). -/
theorem polynomial_193_typeI_progression (t : ℕ) :
    Nat.Coprime 193 140 ∧
      1 ≤ 50 + 35 * t ∧
      50 + 35 * t < 1450 + 2065 * t + 735 * t ^ 2 ∧
      1450 + 2065 * t + 735 * t ^ 2 <
        27985 + 40565 * t + 14700 * t ^ 2 ∧
      (4 / (193 + 140 * t) : ℚ) = 1 / (50 + 35 * t) +
        1 / (1450 + 2065 * t + 735 * t ^ 2) +
        1 / (27985 + 40565 * t + 14700 * t ^ 2) := by
  let N := 193 + 140 * t
  let X := 50 + 35 * t
  let Y := 1450 + 2065 * t + 735 * t ^ 2
  let Z := 27985 + 40565 * t + 14700 * t ^ 2
  have hN : 0 < N := by dsimp [N]; omega
  have hX : 0 < X := by dsimp [X]; omega
  have hY : 0 < Y := by dsimp [Y]; omega
  have hZ : 0 < Z := by dsimp [Z]; omega
  have hXY : X < Y := by dsimp [X, Y]; omega
  have hYZ : Y < Z := by dsimp [Y, Z]; omega
  have hpoly : 4 * X * Y * Z = N * (X * Y + X * Z + Y * Z) := by
    dsimp [N, X, Y, Z]
    ring
  have hpolyQ : 4 * (X : ℚ) * Y * Z = N * (X * Y + X * Z + Y * Z) := by
    exact_mod_cast hpoly
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hXq : (X : ℚ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  have hYq : (Y : ℚ) ≠ 0 := by exact_mod_cast (by omega : Y ≠ 0)
  have hZq : (Z : ℚ) ≠ 0 := by exact_mod_cast (by omega : Z ≠ 0)
  have hfrac : (4 / N : ℚ) = 1 / X + 1 / Y + 1 / Z := by
    field_simp
    nlinarith only [hpolyQ]
  exact ⟨by decide, by change 1 ≤ X; omega, by simpa only [X, Y] using hXY,
    by simpa only [Y, Z] using hYZ,
    by simpa only [N, X, Y, Z, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hfrac⟩


end Erdos242
