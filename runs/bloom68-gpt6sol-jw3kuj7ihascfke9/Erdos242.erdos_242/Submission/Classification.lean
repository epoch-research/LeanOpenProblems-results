import Submission.Reduction

/-!
# Ordered prime divisor classification for Erdős–Straus

For a prime `p > 2`, an ordered decomposition has `p < 4x`, `2x < p`, and
`p ∣ z`. Conversely, `Good p` is equivalent to either of two exact divisor
conditions on such an `x` (`TypeI` and `TypeII`). The constructions use the
quotients in `Submission/IndependentNotes.md` and retain strict order.

This classifies conditional witnesses; it does **not** establish `Good p` for
all primes or resolve the conjecture in `Submission/Spec.lean`.
-/

namespace Erdos242

private theorem fraction_iff_polynomial (p x y z : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (4 / p : ℚ) = 1 / x + 1 / y + 1 / z ↔
      4 * x * y * z = p * (x * y + x * z + y * z) := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast (by omega : x ≠ 0)
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast (by omega : y ≠ 0)
  have hzq : (z : ℚ) ≠ 0 := by exact_mod_cast (by omega : z ≠ 0)
  have hf : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z ↔
       4 * (x : ℚ) * y * z = p * (x * y + x * z + y * z) := by
    field_simp
    constructor <;> intro h <;> nlinarith [h]
  constructor
  · intro h
    exact_mod_cast hf.mp h
  · intro h
    apply hf.mpr
    exact_mod_cast h

private theorem ordered_first_bounds (p x y z : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p < 4 * x ∧ x < p := by
  have hxp : (0 : ℚ) < x := by exact_mod_cast hx
  have hpp : (0 : ℚ) < p := by exact_mod_cast hp
  have hyp : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
  have hzp : (0 : ℚ) < z := by exact_mod_cast (by omega : 0 < z)
  have hxyq : (x : ℚ) < y := by exact_mod_cast hxy
  have hxzq : (x : ℚ) < z := by exact_mod_cast (by omega : x < z)
  have hfirst : (1 / (x : ℚ)) < 4 / p := by
    rw [heq]
    have : (0 : ℚ) < 1 / y := by positivity
    have : (0 : ℚ) < 1 / z := by positivity
    linarith
  have hlast : 4 / (p : ℚ) < 3 / x := by
    rw [heq]
    have h1 : (1 / (y : ℚ)) < 1 / x := one_div_lt_one_div_of_lt hxp hxyq
    have h2 : (1 / (z : ℚ)) < 1 / x := one_div_lt_one_div_of_lt hxp hxzq
    have h3 : (3 / (x : ℚ)) = 1 / x + 1 / x + 1 / x := by ring
    rw [h3]
    linarith
  have hlt1 : (p : ℚ) < 4 * x := by
    simpa only [one_mul] using (div_lt_div_iff₀ hxp hpp).mp hfirst
  have hlt2 : 4 * (x : ℚ) < 3 * p :=
    (div_lt_div_iff₀ hpp hxp).mp hlast
  constructor
  · exact_mod_cast hlt1
  · have : (x : ℚ) < p := by linarith
    exact_mod_cast this

/-- A prime greater than two cannot divide four. -/
private theorem prime_not_dvd_four (p : ℕ) (hp : p.Prime) (hgt : 2 < p) : ¬p ∣ 4 := by
  intro hfour
  have h22 : p ∣ 2 * 2 := by simpa using hfour
  have h2 : p ∣ 2 := ((hp.dvd_mul).mp h22).elim id id
  exact (Nat.not_dvd_of_pos_of_lt (by norm_num) hgt) h2

/-- In an ordered solution for prime `p > 2`, the last denominator is divisible by `p`. -/
theorem prime_dvd_last (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : p ∣ z := by
  have hpoly := (fraction_iff_polynomial p x y z (by omega) hx (by omega) (by omega)).mp heq
  have hxltp := (ordered_first_bounds p x y z (by omega) hx hxy hyz heq).2
  have hnotx : ¬ p ∣ x := Nat.not_dvd_of_pos_of_lt hx hxltp
  have hpdxyz : p ∣ x * y * z := by
    have hfour : p ∣ 4 * (x * y * z) := by
      rw [show 4 * (x * y * z) = 4 * x * y * z by ring, hpoly]
      exact dvd_mul_right p _
    exact ((hp.dvd_mul).mp hfour).resolve_left (prime_not_dvd_four p hp hgt)
  by_contra hnotz
  have hpdy : p ∣ y := by
    have hpd : p ∣ x * (y * z) := by simpa only [mul_assoc] using hpdxyz
    rcases (hp.dvd_mul).mp hpd with hpx | hpyz
    · exact False.elim (hnotx hpx)
    · rcases (hp.dvd_mul).mp hpyz with hpy | hpz
      · exact hpy
      · exact False.elim (hnotz hpz)
  obtain ⟨m, rfl⟩ := hpdy
  have hm : 0 < m := by
    by_contra hzero
    have : m = 0 := by omega
    subst m
    simp at hxy
  have hpoly2 : 4 * x * m * z = x * p * m + x * z + p * m * z := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
    nlinarith [hpoly]
  let h := 4 * m - 1
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hprod : h * x * z = p * m * (x + z) := by
    nlinarith [congrArg (fun n : ℕ => n * x * z) hh, hpoly2]
  have hpdh : p ∣ h := by
    have hphxz : p ∣ h * (x * z) := by
      rw [← mul_assoc, hprod]
      simpa only [mul_assoc] using (dvd_mul_right p (m * (x + z)))
    rcases (hp.dvd_mul).mp hphxz with hph | hpxz
    · exact hph
    · rcases (hp.dvd_mul).mp hpxz with hpx | hpz
      · exact False.elim (hnotx hpx)
      · exact False.elim (hnotz hpz)
  obtain ⟨k, hk⟩ := hpdh
  have hkprod : k * x * z = m * (x + z) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
    calc
      p * (k * x * z) = h * x * z := by rw [hk]; ring
      _ = p * m * (x + z) := hprod
      _ = p * (m * (x + z)) := by ring
  have hkm : m < k * x := by
    by_contra hne
    have hle : k * x * z ≤ m * z := Nat.mul_le_mul_right z (by omega)
    nlinarith [hkprod, Nat.mul_pos hm hx]
  have hzle : z ≤ m * x := by
    have hle : (m + 1) * z ≤ (k * x) * z :=
      Nat.mul_le_mul_right z (by omega)
    nlinarith [hkprod]
  have hmx : m * x < p * m := by
    simpa only [mul_comm p m] using Nat.mul_lt_mul_of_pos_left hxltp hm
  omega

/-- The two positive factors associated to an ordered solution. -/
private theorem ordered_factors (p x y z : ℕ)
    (hp : 0 < p) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    let a := 4 * x - p
    let N := p * x
    0 < a ∧ N < a * y ∧ N < a * z ∧
      (a * y - N) * (a * z - N) = N ^ 2 := by
  dsimp
  have hpbound := (ordered_first_bounds p x y z hp hx hxy hyz heq).1
  let a := 4 * x - p
  let N := p * x
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hpoly := (fraction_iff_polynomial p x y z hp hx (by omega) (by omega)).mp heq
  have halg : a * y * z = N * (y + z) := by
    dsimp [N]
    nlinarith [hpoly, congrArg (fun t : ℕ => t * y * z) haeq]
  have hN : 0 < N := Nat.mul_pos hp hx
  have hNy : N < a * y := by
    apply (Nat.mul_lt_mul_right (by omega : 0 < z)).mp
    nlinarith [halg, Nat.mul_pos hN (by omega : 0 < y)]
  have hNz : N < a * z := by
    apply (Nat.mul_lt_mul_right (by omega : 0 < y)).mp
    nlinarith [halg, Nat.mul_pos hN (by omega : 0 < z)]
  let d := a * y - N
  let e := a * z - N
  have hd : d + N = a * y := Nat.sub_add_cancel (by omega)
  have he : e + N = a * z := Nat.sub_add_cancel (by omega)
  have hsum : d + e + 2 * N = a * (y + z) := by nlinarith [hd, he]
  have hprod : (d + N) * (e + N) = N * (a * (y + z)) := by
    calc
      (d + N) * (e + N) = (a * y) * (a * z) := by rw [hd, he]
      _ = a * (a * y * z) := by ring
      _ = a * (N * (y + z)) := by rw [halg]
      _ = N * (a * (y + z)) := by ring
  have hfac : d * e = N ^ 2 := by
    nlinarith [hprod, congrArg (fun t : ℕ => N * t) hsum]
  exact ⟨ha, hNy, hNz, hfac⟩

/-- A prime `p` is coprime to the first denominator, hence so is `4x-p` to `px`. -/
private theorem prime_coprime_shift (p x : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxlt : x < p) (hpx : p < 4 * x) :
    (4 * x - p).Coprime (p * x) := by
  let a := 4 * x - p
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hnotx : ¬p ∣ x := Nat.not_dvd_of_pos_of_lt hx hxlt
  have hnotfour : ¬p ∣ 4 := prime_not_dvd_four p hp hgt
  have hnotpa : ¬p ∣ a := by
    intro hpa
    have hd : p ∣ 4 * x := by rw [←haeq]; exact dvd_add hpa (dvd_refl p)
    rcases (hp.dvd_mul).mp hd with h4 | hx'
    · exact hnotfour h4
    · exact hnotx hx'
  have hax : a.Coprime x := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqx
    have hq4x : q ∣ 4 * x := hqx.mul_left 4
    have hqp : q ∣ p := by
      have hap : q ∣ a + p := by rw [haeq]; exact hq4x
      exact (Nat.dvd_add_iff_left hqa).mpr (by simpa only [add_comm] using hap)
    have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    exact hnotx (hqp_eq ▸ hqx)
  have hap : a.Coprime p := ((hp.coprime_iff_not_dvd).mpr hnotpa).symm
  exact hap.mul_right hax

/-- The first (non-`p`-divisible middle denominator) divisor condition. -/
def TypeI (p x : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧ (4 * x - p) ∣ 4 * c + 1

/-- The second (`p`-divisible middle denominator) divisor condition. -/
def TypeII (p x : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ d < x ∧ d ∣ x ^ 2 ∧ (4 * x - p) ∣ x + d

/-- In the type-I case, the divisor is exactly the complementary factor. -/
theorem typeI_factor_of_ordered (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z)
    (hnoty : ¬p ∣ y) :
    ∃ c : ℕ, 0 < c ∧ ((4 * x - p) * y - p * x) * c = x ^ 2 ∧
      (4 * x - p) ∣ 4 * c + 1 := by
  let a := 4 * x - p
  let N := p * x
  let d := a * y - N
  let e := a * z - N
  have hfactors := ordered_factors p x y z (by omega) hx hxy hyz heq
  change 0 < a ∧ N < a * y ∧ N < a * z ∧ d * e = N ^ 2 at hfactors
  obtain ⟨ha, hNy, hNz, hfac⟩ := hfactors
  have hd : d + N = a * y := Nat.sub_add_cancel (by omega)
  obtain ⟨hpx, hxltp⟩ := ordered_first_bounds p x y z (by omega) hx hxy hyz heq
  have hcopN : a.Coprime N := prime_coprime_shift p x hp hgt hx hxltp hpx
  have hnotpa : ¬p ∣ a := by
    intro hpa
    have hcop : p.Coprime N := hcopN.of_dvd_left hpa
    have hpone : p = 1 := hcop.eq_one_of_dvd (by dsimp [N]; exact dvd_mul_right p x)
    omega
  have hnotd : ¬p ∣ d := by
    intro hpd
    have hpay : p ∣ a * y := by
      rw [← hd]
      exact dvd_add hpd (by dsimp [N]; exact dvd_mul_right p x)
    rcases (hp.dvd_mul).mp hpay with hpa | hpy
    · exact hnotpa hpa
    · exact hnoty hpy
  have hdvd : d ∣ x ^ 2 := by
    have hcopdp : d.Coprime (p ^ 2) :=
      (((hp.coprime_iff_not_dvd).mpr hnotd).symm).pow_right 2
    have hdiv : d ∣ p ^ 2 * x ^ 2 := by
      have : d ∣ N ^ 2 := by rw [← hfac]; exact dvd_mul_right d e
      simpa only [N, mul_pow] using this
    exact hcopdp.dvd_of_dvd_mul_left hdiv
  let c := x ^ 2 / d
  have hdc : d * c = x ^ 2 := Nat.mul_div_cancel' hdvd
  have hcpos : 0 < c := by
    have hxpow : 0 < x ^ 2 := pow_pos hx 2
    rcases Nat.eq_zero_or_pos c with hc0 | hc
    · rw [hc0] at hdc
      simp at hdc
      omega
    · exact hc
  have hcopd : a.Coprime d := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqd
    have hqN : q ∣ N := by
      have hqdy : q ∣ d + N := by rw [hd]; exact hqa.mul_right y
      exact (Nat.dvd_add_iff_right hqd).mpr hqdy
    have hqc : q.Coprime N := hcopN.of_dvd_left hqa
    have hqone : q = 1 := hqc.eq_one_of_dvd hqN
    exact (ne_of_gt hq.one_lt) hqone
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hdivmul : a ∣ d * (4 * c + 1) := by
    have hmuleq : d * (4 * c + 1) = a * (x + y) := by
      dsimp [N] at hd
      nlinarith [hd, hdc, congrArg (fun t : ℕ => t * x) haeq]
    rw [hmuleq]
    exact dvd_mul_right a _
  exact ⟨c, hcpos, hdc, hcopd.dvd_of_dvd_mul_left hdivmul⟩

/-- The non-`p`-divisible middle denominator yields a type-I divisor. -/
theorem typeI_of_ordered (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z)
    (hnoty : ¬p ∣ y) : TypeI p x := by
  obtain ⟨c, hc, hdc, hdiv⟩ := typeI_factor_of_ordered p x y z hp hgt hx hxy hyz heq hnoty
  refine ⟨c, hc, ?_, hdiv⟩
  rw [← hdc]
  exact dvd_mul_left c _

/-- If the middle denominator is a multiple of `p`, an ordered solution yields type II. -/
theorem typeII_of_ordered (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z)
    (hpy : p ∣ y) : TypeII p x := by
  have hpz : p ∣ z := prime_dvd_last p x y z hp hgt hx hxy hyz heq
  obtain ⟨m, rfl⟩ := hpy
  obtain ⟨u, rfl⟩ := hpz
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := by omega
    subst m
    simp at hxy
  have hu : 0 < u := by
    by_contra hu0
    have : u = 0 := by omega
    subst u
    simp at hyz
  have hmu : m < u := by
    apply (Nat.mul_lt_mul_left (by omega : 0 < p)).mp
    exact hyz
  let a := 4 * x - p
  have hpx := (ordered_first_bounds p x (p * m) (p * u) (by omega) hx hxy hyz heq).1
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hpoly := (fraction_iff_polynomial p x (p * m) (p * u) (by omega) hx
    (by omega) (by omega)).mp heq
  have hpoly2 : 4 * x * m * u = x * (m + u) + p * m * u := by
    apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < p ^ 2)
    nlinarith [hpoly]
  have hrel : a * m * u = x * (m + u) := by
    nlinarith [hpoly2, congrArg (fun t : ℕ => t * m * u) haeq]
  have hxm : x < a * m := by
    apply (Nat.mul_lt_mul_right hu).mp
    nlinarith [hrel, Nat.mul_pos hx hm]
  have hxu : x < a * u := by
    apply (Nat.mul_lt_mul_right hm).mp
    nlinarith [hrel, Nat.mul_pos hx hu]
  let d := a * m - x
  let b := a * u - x
  have hd : d + x = a * m := Nat.sub_add_cancel (by omega)
  have hb : b + x = a * u := Nat.sub_add_cancel (by omega)
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdb : d < b := by
    have : a * m < a * u := Nat.mul_lt_mul_of_pos_left hmu ha
    omega
  have hsum : d + b + 2 * x = a * (m + u) := by nlinarith [hd, hb]
  have hprod : (d + x) * (b + x) = x * (a * (m + u)) := by
    calc
      (d + x) * (b + x) = (a * m) * (a * u) := by rw [hd, hb]
      _ = a * (a * m * u) := by ring
      _ = a * (x * (m + u)) := by rw [hrel]
      _ = x * (a * (m + u)) := by ring
  have hdbprod : d * b = x ^ 2 := by
    nlinarith only [hprod, congrArg (fun t : ℕ => x * t) hsum]
  have hdx : d < x := by
    have hdsq : d ^ 2 < x ^ 2 := by
      nlinarith only [Nat.mul_lt_mul_of_pos_left hdb hdpos, hdbprod]
    exact (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hdsq
  have hdvd : d ∣ x ^ 2 := by rw [← hdbprod]; exact dvd_mul_right d b
  have haadd : a ∣ x + d := by rw [add_comm, hd]; exact dvd_mul_right a m
  exact ⟨d, hdpos, hdx, hdvd, haadd⟩

/-- In every ordered prime solution, the first denominator lies strictly below `p/2`. -/
theorem prime_first_below_half (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : 2 * x < p := by
  have hxltp := (ordered_first_bounds p x y z (by omega) hx hxy hyz heq).2
  by_contra hnot
  have htwox : p ≤ 2 * x := by omega
  have hyltn : y < p := by
    have hxp : (0 : ℚ) < x := by exact_mod_cast hx
    have hpp : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
    have hyp : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
    have hzq : (y : ℚ) < z := by exact_mod_cast hyz
    have hxratio : 1 / (x : ℚ) ≤ 2 / p := by
      apply (div_le_div_iff₀ hxp hpp).mpr
      simpa only [one_mul] using (show (p : ℚ) ≤ 2 * x by exact_mod_cast htwox)
    have hzr : 1 / (z : ℚ) < 1 / y := one_div_lt_one_div_of_lt hyp hzq
    have hsum : (2 / (p : ℚ)) < 2 / y := by
      have h4 : (4 / (p : ℚ)) = 2 * (2 / p) := by ring
      have h2 : (2 / (y : ℚ)) = 2 * (1 / y) := by ring
      rw [h4] at heq
      rw [h2]
      linarith
    have hyltr : (y : ℚ) < p := by
      have hmul := (div_lt_div_iff₀ hpp hyp).mp hsum
      nlinarith
    exact_mod_cast hyltr
  have hnoty : ¬p ∣ y := Nat.not_dvd_of_pos_of_lt (by omega) hyltn
  obtain ⟨c, hc, hdc, hdiv⟩ :=
    typeI_factor_of_ordered p x y z hp hgt hx hxy hyz heq hnoty
  let a := 4 * x - p
  let d := a * y - p * x
  have hfactors := ordered_factors p x y z (by omega) hx hxy hyz heq
  have hNy : p * x < a * y := hfactors.2.1
  have hd : d + p * x = a * y := Nat.sub_add_cancel (by omega)
  have ha : 0 < a := by dsimp [a]; omega
  have hne : p ≠ 2 * x := by
    intro hpeq
    have hp2x : p ∣ 2 * x := by rw [← hpeq]
    rcases (hp.dvd_mul).mp hp2x with htwo | hxx
    · exact (Nat.not_dvd_of_pos_of_lt (by omega : 0 < 2) (by omega : 2 < p)) htwo
    · exact (Nat.not_dvd_of_pos_of_lt hx hxltp) hxx
  have hap2 : p + 2 ≤ a := by dsimp [a]; omega
  have hax : a * x < a * y := Nat.mul_lt_mul_of_pos_left hxy ha
  have hpax : (p + 2) * x ≤ a * x := Nat.mul_le_mul_right x hap2
  have hdgt : 2 * x < d := by nlinarith only [hpax, hax, hd]
  have hcx : 2 * c < x := by
    apply (Nat.mul_lt_mul_left hx).mp
    nlinarith only [hdc, Nat.mul_lt_mul_of_pos_right hdgt hc]
  have hsmall : 4 * c + 1 < a := by dsimp [a]; omega
  exact (Nat.not_dvd_of_pos_of_lt (by omega) hsmall) hdiv

/-- The complete structural bound for any ordered solution at prime `p > 2`.
The inequalities say `p/4 < x < p/2` without dividing in `ℕ`. -/
theorem ordered_solution_bounds (p x y z : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (heq : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) :
    p < 4 * x ∧ 2 * x < p ∧ p ∣ z :=
  ⟨(ordered_first_bounds p x y z (by omega) hx hxy hyz heq).1,
   prime_first_below_half p x y z hp hgt hx hxy hyz heq,
   prime_dvd_last p x y z hp hgt hx hxy hyz heq⟩

/-- A positive factorization `d e=(px)²` gives the unit-fraction identity. -/
private theorem good_of_factors (p x y z a d e : ℕ)
    (hp : 0 < p) (hx : 0 < x) (ha : 0 < a)
    (haeq : a + p = 4 * x) (hxy : x < y) (hyz : y < z)
    (hdy : a * y = p * x + d) (hdz : a * z = p * x + e)
    (hde : d * e = (p * x) ^ 2) : Good p := by
  let N := p * x
  have hdyN : a * y = N + d := hdy
  have hdzN : a * z = N + e := hdz
  have hdeN : d * e = N ^ 2 := hde
  have hsum : d + e + 2 * N = a * (y + z) := by
    nlinarith only [hdyN, hdzN]
  have hfprod : (d + N) * (e + N) = N * (d + e + 2 * N) := by
    nlinarith only [hdeN]
  have hcancel : a * (a * y * z) = a * (N * (y + z)) := by
    calc
      a * (a * y * z) = (a * y) * (a * z) := by ring
      _ = (d + N) * (e + N) := by rw [hdy, hdz]; ring
      _ = N * (d + e + 2 * N) := hfprod
      _ = a * (N * (y + z)) := by rw [hsum]; ring
  have hrel : a * y * z = N * (y + z) := Nat.eq_of_mul_eq_mul_left ha hcancel
  have hpoly : 4 * x * y * z = p * (x * y + x * z + y * z) := by
    dsimp [N] at hrel
    nlinarith only [hrel, congrArg (fun t : ℕ => t * y * z) haeq]
  refine ⟨x, y, z, by omega, hxy, hyz, ?_⟩
  exact (fraction_iff_polynomial p x y z hp hx (by omega) (by omega)).mpr hpoly

/-- The type-I divisor produces the ordered denominators
`x, (px + x²/c)/a, (px + p²c)/a`, where `a=4x-p`. -/
theorem good_of_typeI (p x : ℕ) (hp : 0 < p)
    (hlo : p < 4 * x) (hhi : 2 * x < p) (hI : TypeI p x) : Good p := by
  obtain ⟨c, hc, hcx, hacdiv⟩ := hI
  let a := 4 * x - p
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have halp : a < p := by dsimp [a]; omega
  have hx : 0 < x := by omega
  have hxltp : x < p := by omega
  let d := x ^ 2 / c
  have hcd : c * d = x ^ 2 := Nat.mul_div_cancel' hcx
  have hac : a.Coprime c := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqc
    have hqf : q ∣ 4 * c + 1 := dvd_trans hqa hacdiv
    have hq4c : q ∣ 4 * c := hqc.mul_left 4
    have hq1 : q ∣ 1 := by
      have hh := Nat.dvd_sub hqf hq4c
      simpa only [Nat.add_sub_cancel_left] using hh
    have heq : q = 1 := Nat.dvd_one.mp hq1
    exact (ne_of_gt hq.one_lt) heq
  have hdivy : a ∣ p * x + d := by
    have hkey : c * (p * x + d) + a * (x * c) = x ^ 2 * (4 * c + 1) := by
      nlinarith only [hcd, congrArg (fun t : ℕ => t * x * c) haeq]
    have hdiv : a ∣ c * (p * x + d) := by
      have htotal : a ∣ c * (p * x + d) + a * (x * c) := by
        rw [hkey]
        exact hacdiv.mul_left (x ^ 2)
      exact (Nat.dvd_add_iff_left (dvd_mul_right a (x * c))).mpr htotal
    exact hac.dvd_of_dvd_mul_left hdiv
  have hdivz : a ∣ p * x + p ^ 2 * c := by
    have hsq : (4 * x) ^ 2 = p ^ 2 + a * (p + 4 * x) := by
      nlinarith only [congrArg (fun t : ℕ => t * (p + 4 * x)) haeq]
    have hkey : (p * x + p ^ 2 * c) + a * (x + (p + 4 * x) * c) =
        4 * x ^ 2 * (4 * c + 1) := by
      nlinarith only [congrArg (fun t : ℕ => t * x) haeq,
        congrArg (fun t : ℕ => t * c) hsq]
    have htotal : a ∣ (p * x + p ^ 2 * c) + a * (x + (p + 4 * x) * c) := by
      rw [hkey]
      exact hacdiv.mul_left (4 * x ^ 2)
    exact (Nat.dvd_add_iff_left (dvd_mul_right a _)).mpr htotal
  let y := (p * x + d) / a
  let z := (p * x + p ^ 2 * c) / a
  have hy : a * y = p * x + d := Nat.mul_div_cancel' hdivy
  have hz : a * z = p * x + p ^ 2 * c := Nat.mul_div_cancel' hdivz
  have hxy : x < y := by
    have hax : a * x < p * x := Nat.mul_lt_mul_of_pos_right halp hx
    apply (Nat.mul_lt_mul_left ha).mp
    exact lt_of_lt_of_le hax (by rw [hy]; exact Nat.le_add_right (p * x) d)
  have hd_le : d ≤ x ^ 2 := by
    calc
      d = 1 * d := by simp
      _ ≤ c * d := Nat.mul_le_mul_right d hc
      _ = x ^ 2 := hcd
  have hd_lt : d < p ^ 2 * c := by
    have hxp : x ^ 2 < p ^ 2 :=
      (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mpr hxltp
    have hpc : p ^ 2 ≤ p ^ 2 * c := by
      have hcle : 1 ≤ c := by omega
      simpa using Nat.mul_le_mul_left (p ^ 2) hcle
    omega
  have hyz : y < z := by
    apply (Nat.mul_lt_mul_left ha).mp
    omega
  have hfac : d * (p ^ 2 * c) = (p * x) ^ 2 := by
    calc
      d * (p ^ 2 * c) = p ^ 2 * (c * d) := by ring
      _ = p ^ 2 * x ^ 2 := by rw [hcd]
      _ = (p * x) ^ 2 := by ring
  exact good_of_factors p x y z a d (p ^ 2 * c) hp hx ha haeq hxy hyz hy hz hfac

/-- The type-II divisor produces the ordered denominators
`x, p (x+d)/a, p (x+x²/d)/a`, where `a=4x-p`. -/
theorem good_of_typeII (p x : ℕ) (hp : p.Prime) (hgt : 2 < p)
    (hlo : p < 4 * x) (hhi : 2 * x < p) (hII : TypeII p x) : Good p := by
  obtain ⟨d, hd, hdx, hdxsq, hadiv⟩ := hII
  let a := 4 * x - p
  have hpp : 0 < p := by omega
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have halp : a < p := by dsimp [a]; omega
  have hx : 0 < x := lt_trans hd hdx
  have hxltp : x < p := by omega
  have hax : a.Coprime x :=
    (prime_coprime_shift p x hp hgt hx hxltp hlo).of_dvd_right (dvd_mul_left x p)
  let b := x ^ 2 / d
  have hdbprod : d * b = x ^ 2 := Nat.mul_div_cancel' hdxsq
  have hdb : d < b := by
    have hdsq : d ^ 2 < x ^ 2 :=
      (Nat.pow_lt_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mpr hdx
    apply (Nat.mul_lt_mul_left hd).mp
    nlinarith only [hdsq, hdbprod]
  have had : a.Coprime d := by
    apply Nat.coprime_of_dvd
    intro q hq hqa hqd
    have hqxd : q ∣ x + d := dvd_trans hqa hadiv
    have hqx : q ∣ x := (Nat.dvd_add_iff_left hqd).mpr hqxd
    have hqc : q.Coprime x := hax.of_dvd_left hqa
    have heq : q = 1 := hqc.eq_one_of_dvd hqx
    exact (ne_of_gt hq.one_lt) heq
  have habdiv : a ∣ x + b := by
    have heq : d * (x + b) = x * (x + d) := by nlinarith only [hdbprod]
    have hmul : a ∣ d * (x + b) := by
      rw [heq]
      exact hadiv.mul_left x
    exact had.dvd_of_dvd_mul_left hmul
  let m := (x + d) / a
  let u := (x + b) / a
  have hm : a * m = x + d := Nat.mul_div_cancel' hadiv
  have hu : a * u = x + b := Nat.mul_div_cancel' habdiv
  have hxm : x < a * m := by omega
  have hapm : a * m ≤ p * m := Nat.mul_le_mul_right m (by omega)
  have hxy : x < p * m := lt_of_lt_of_le hxm hapm
  have hmu : m < u := by
    apply (Nat.mul_lt_mul_left ha).mp
    omega
  have hyz : p * m < p * u := Nat.mul_lt_mul_of_pos_left hmu hpp
  have hdy : a * (p * m) = p * x + p * d := by
    calc
      a * (p * m) = p * (a * m) := by ring
      _ = p * (x + d) := by rw [hm]
      _ = p * x + p * d := by ring
  have hdz : a * (p * u) = p * x + p * b := by
    calc
      a * (p * u) = p * (a * u) := by ring
      _ = p * (x + b) := by rw [hu]
      _ = p * x + p * b := by ring
  have hprod : (p * d) * (p * b) = (p * x) ^ 2 := by
    calc
      (p * d) * (p * b) = p ^ 2 * (d * b) := by ring
      _ = p ^ 2 * x ^ 2 := by rw [hdbprod]
      _ = (p * x) ^ 2 := by ring
  exact good_of_factors p x (p * m) (p * u) a (p * d) (p * b)
    hpp hx ha haeq hxy hyz hdy hdz hprod

/-- Exact necessary-and-sufficient ordered prime divisor criterion.
The two alternatives are genuinely different: type I need not have `p ∣ y`. -/
theorem good_iff_ordered_divisors (p : ℕ) (hp : p.Prime) (hgt : 2 < p) :
    Good p ↔ ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ (TypeI p x ∨ TypeII p x) := by
  constructor
  · rintro ⟨x, y, z, hx, hxy, hyz, heq⟩
    have hxpos : 0 < x := by omega
    have hlow := (ordered_first_bounds p x y z (by omega) hxpos hxy hyz heq).1
    have hhigh := prime_first_below_half p x y z hp hgt hxpos hxy hyz heq
    refine ⟨x, hlow, hhigh, ?_⟩
    by_cases hpy : p ∣ y
    · exact Or.inr (typeII_of_ordered p x y z hp hgt hxpos hxy hyz heq hpy)
    · exact Or.inl (typeI_of_ordered p x y z hp hgt hxpos hxy hyz heq hpy)
  · rintro ⟨x, hlow, hhigh, hcases⟩
    rcases hcases with hI | hII
    · exact good_of_typeI p x (by omega) hlow hhigh hI
    · exact good_of_typeII p x hp hgt hlow hhigh hII

/-- The same criterion stated with the two divisibility alternatives expanded. -/
theorem good_iff_explicit_divisors (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    Good p ↔ ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧
      ((∃ c : ℕ, 0 < c ∧ c ∣ x ^ 2 ∧ (4 * x - p) ∣ 4 * c + 1) ∨
       (∃ d : ℕ, 0 < d ∧ d < x ∧ d ∣ x ^ 2 ∧ (4 * x - p) ∣ x + d)) := by
  simpa only [TypeI, TypeII] using good_iff_ordered_divisors p hp (by omega : 2 < p)

end Erdos242