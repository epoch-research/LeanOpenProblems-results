import Submission.Reduction

/-!
# Arithmetic certificates for three distinct Erdős–Straus denominators

The two certificates below use the modulus `m = 4 * x - p`.  Divisibility is
proved in `ℕ`, before the resulting exact quotients are cast to `ℚ`.  The
witness lemmas record the prescribed denominators in strictly increasing order.
-/

namespace Erdos242Aux

/-- Bounds, congruence, and coprimality of the certificate modulus. -/
lemma certificate_modulus_facts (p x : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpx : p < 4 * x) (hxp : 2 * x < p) :
    3 ≤ 4 * x - p ∧ 4 * x - p < p ∧ x < p ∧ (4 * x - p) % 4 = 3 ∧
      Nat.Coprime (4 * x - p) x ∧ Nat.Coprime (4 * x - p) p := by
  have hsum : (4 * x - p) + p = 4 * x := by omega
  have hlt : 4 * x - p < p := by omega
  have hmod : (4 * x - p) % 4 = 3 := by omega
  have hm3 : 3 ≤ 4 * x - p := by omega
  have hmp : Nat.Coprime (4 * x - p) p :=
    (Nat.coprime_of_lt_prime (by omega) hlt hp).symm
  have hm4x : Nat.Coprime (4 * x - p) (4 * x) := by
    simpa only [hsum] using (Nat.coprime_self_add_right.mpr hmp)
  have hmx : Nat.Coprime (4 * x - p) x :=
    (Nat.coprime_mul_iff_right.mp hm4x).2
  exact ⟨hm3, hlt, by omega, hmod, hmx, hmp⟩

/-- In particular, both gcds requested by the certificates are one. -/
lemma certificate_modulus_gcd (p x : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hpx : p < 4 * x) (hxp : 2 * x < p) :
    Nat.gcd (4 * x - p) x = 1 ∧ Nat.gcd (4 * x - p) p = 1 := by
  obtain ⟨_, _, _, _, hmx, hmp⟩ := certificate_modulus_facts p x hp hp4 hpx hxp
  exact ⟨hmx.gcd_eq_one, hmp.gcd_eq_one⟩

/-- An exact quotient of positive natural numbers is positive. -/
lemma positive_quotient_of_dvd (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdiv : b ∣ a) : 0 < a / b :=
  Nat.div_pos (Nat.le_of_dvd ha hdiv) hb

/-- The two numerators in Certificate I are divisible by the modulus.
Here `e` is the natural quotient `x² / d`, represented by its exact product. -/
lemma certificate_I_divisibility (p x d e m : ℕ) (hsum : m + p = 4 * x)
    (hmx : Nat.Coprime m x) (hde : d * e = x ^ 2) (hdiv : m ∣ 4 * d + 1) :
    m ∣ p * x + e ∧ m ∣ p * (x + p * d) := by
  have hd : d ∣ x ^ 2 := ⟨e, hde.symm⟩
  have hmd : Nat.Coprime m d := (hmx.pow_right 2).of_dvd_right hd
  have hb : m ∣ x + p * d := by
    apply (Nat.dvd_add_iff_right (Nat.dvd_mul_right m d)).mpr
    have heq : m * d + (x + p * d) = x * (4 * d + 1) := by
      calc
        m * d + (x + p * d) = (m + p) * d + x := by ring
        _ = x * (4 * d + 1) := by rw [hsum]; ring
    rw [heq]
    exact dvd_mul_of_dvd_right hdiv x
  have ha : m ∣ d * (p * x + e) := by
    have heq : d * (p * x + e) = x * (x + p * d) := by
      calc
        d * (p * x + e) = p * d * x + d * e := by ring
        _ = x * (x + p * d) := by rw [hde]; ring
    rw [heq]
    exact dvd_mul_of_dvd_right hb x
  exact ⟨hmd.dvd_of_dvd_mul_left ha, dvd_mul_of_dvd_right hb p⟩

/-- The two numerators in Certificate II are divisible by the modulus. -/
lemma certificate_II_divisibility (p x d e m : ℕ) (hmx : Nat.Coprime m x)
    (hde : d * e = x ^ 2) (hdiv : m ∣ x + d) :
    m ∣ p * (x + d) ∧ m ∣ p * (x + e) := by
  have hd : d ∣ x ^ 2 := ⟨e, hde.symm⟩
  have hmd : Nat.Coprime m d := (hmx.pow_right 2).of_dvd_right hd
  have hb : m ∣ x + e := by
    apply hmd.dvd_of_dvd_mul_left
    have heq : d * (x + e) = x * (x + d) := by
      calc
        d * (x + e) = d * x + d * e := by ring
        _ = x * (x + d) := by rw [hde]; ring
    rw [heq]
    exact dvd_mul_of_dvd_right hdiv x
  exact ⟨dvd_mul_of_dvd_right hdiv p, dvd_mul_of_dvd_right hb p⟩

/-- The cleared ratio `z / y = p * d / x` in Certificate I. -/
lemma certificate_I_ratio (p x d e m y z : ℕ) (hm : 0 < m)
    (hde : d * e = x ^ 2) (hy : m * y = p * x + e)
    (hz : m * z = p * (x + p * d)) : x * z = p * d * y := by
  apply Nat.eq_of_mul_eq_mul_left hm
  calc
    m * (x * z) = x * (m * z) := by ring
    _ = x * (p * (x + p * d)) := by rw [hz]
    _ = p * d * (p * x + e) := by
      calc
        x * (p * (x + p * d)) = p * x ^ 2 + p ^ 2 * d * x := by ring
        _ = p * d * (p * x + e) := by rw [← hde]; ring
    _ = m * (p * d * y) := by rw [← hy]; ring

/-- The rational identity underlying Certificate I. -/
lemma certificate_I_identity (p x d m : ℚ) (hp : 0 < p) (hx : 0 < x)
    (hd : 0 < d) (hm : m = 4 * x - p) :
    4 / p = 1 / x + 1 / ((p * x + x ^ 2 / d) / m) +
      1 / (p * (x + p * d) / m) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hd0 : d ≠ 0 := ne_of_gt hd
  have ha0 : p * x + x ^ 2 / d ≠ 0 := by positivity
  have hb0 : x + p * d ≠ 0 := by positivity
  rw [hm]
  field_simp [hp0, hx0, hd0, ha0, hb0]
  ring

/-- The rational identity underlying Certificate II. -/
lemma certificate_II_identity (p x d m : ℚ) (hp : 0 < p) (hx : 0 < x)
    (hd : 0 < d) (hm : m = 4 * x - p) :
    4 / p = 1 / x + 1 / (p * (x + d) / m) +
      1 / (p * (x + x ^ 2 / d) / m) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hd0 : d ≠ 0 := ne_of_gt hd
  have ha0 : x + d ≠ 0 := by positivity
  have hb0 : x + x ^ 2 / d ≠ 0 := by positivity
  rw [hm]
  field_simp [hp0, hx0, hd0, ha0, hb0]
  ring

/-- Certificate I with its explicit, strictly ordered natural witnesses. -/
theorem certificate_I_witnesses (p x d : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : 0 < x) (hd : 0 < d) (hpx : p < 4 * x) (hxp : 2 * x < p)
    (hdvd : d ∣ x ^ 2) (hdiv : (4 * x - p) ∣ 4 * d + 1) :
    let m := 4 * x - p
    let y := (p * x + x ^ 2 / d) / m
    let z := p * (x + p * d) / m
    1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  let m := 4 * x - p
  let e := x ^ 2 / d
  let y := (p * x + e) / m
  let z := p * (x + p * d) / m
  change 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z
  obtain ⟨hm3, hmltp, hxlt, _, hmx, _⟩ :=
    certificate_modulus_facts p x hp hp4 hpx hxp
  change 3 ≤ m at hm3
  change m < p at hmltp
  change Nat.Coprime m x at hmx
  have hmpos : 0 < m := by omega
  have hpPos : 0 < p := hp.pos
  have hsum : m + p = 4 * x := by dsimp only [m]; omega
  have hde : d * e = x ^ 2 := Nat.mul_div_cancel' hdvd
  have hepos : 0 < e := positive_quotient_of_dvd (x ^ 2) d (by positivity) hd hdvd
  obtain ⟨hdy, hdz⟩ := certificate_I_divisibility p x d e m hsum hmx hde hdiv
  have hypos : 0 < y :=
    positive_quotient_of_dvd (p * x + e) m (by positivity) hmpos hdy
  have hyEq : m * y = p * x + e := Nat.mul_div_cancel' hdy
  have hzEq : m * z = p * (x + p * d) := Nat.mul_div_cancel' hdz
  have hxy : x < y := by
    apply Nat.lt_of_mul_lt_mul_left (a := m)
    rw [hyEq]
    have hlt : m * x < p * x := Nat.mul_lt_mul_of_pos_right hmltp hx
    omega
  have hratio : x * z = p * d * y :=
    certificate_I_ratio p x d e m y z hmpos hde hyEq hzEq
  have hxpd : x < p * d :=
    lt_of_lt_of_le hxlt (Nat.le_mul_of_pos_right p hd)
  have hyz : y < z := by
    apply Nat.lt_of_mul_lt_mul_left (a := x)
    calc
      x * y < p * d * y := Nat.mul_lt_mul_of_pos_right hxpd hypos
      _ = x * z := hratio.symm
  refine ⟨by omega, hxy, hyz, ?_⟩
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hpPos
  have hxQ : (0 : ℚ) < x := by exact_mod_cast hx
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hd0 : (d : ℚ) ≠ 0 := ne_of_gt hdQ
  have hmQ : (m : ℚ) = 4 * (x : ℚ) - p := by
    dsimp only [m]
    rw [Nat.cast_sub (by omega : p ≤ 4 * x)]
    push_cast
    rfl
  have heQ : (e : ℚ) = (x : ℚ) ^ 2 / d := by
    dsimp only [e]
    rw [Nat.cast_div hdvd hd0, Nat.cast_pow]
  have hyQ : (y : ℚ) = ((p : ℚ) * x + e) / m := by
    dsimp only [y]
    rw [Nat.cast_div hdy hm0]
    push_cast
    rfl
  have hzQ : (z : ℚ) = (p : ℚ) * (x + p * d) / m := by
    dsimp only [z]
    rw [Nat.cast_div hdz hm0]
    push_cast
    rfl
  rw [hyQ, hzQ, heQ]
  exact certificate_I_identity (p : ℚ) x d m hpQ hxQ hdQ hmQ

/-- Certificate I: `m ∣ 4*d+1`, where `m = 4*x-p`, suffices for `Distinct p`. -/
theorem certificate_I (p x d : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : 0 < x) (hd : 0 < d) (hpx : p < 4 * x) (hxp : 2 * x < p)
    (hdvd : d ∣ x ^ 2) (hdiv : (4 * x - p) ∣ 4 * d + 1) : Distinct p := by
  exact ⟨x, (p * x + x ^ 2 / d) / (4 * x - p), p * (x + p * d) / (4 * x - p),
    certificate_I_witnesses p x d hp hp4 hx hd hpx hxp hdvd hdiv⟩

/-- Certificate II with its explicit, strictly ordered natural witnesses. -/
theorem certificate_II_witnesses (p x d : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : 0 < x) (hd : 0 < d) (hpx : p < 4 * x) (hxp : 2 * x < p)
    (hdvd : d ∣ x ^ 2) (hdx : d < x) (hdiv : (4 * x - p) ∣ x + d) :
    let m := 4 * x - p
    let y := p * (x + d) / m
    let z := p * (x + x ^ 2 / d) / m
    1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  let m := 4 * x - p
  let e := x ^ 2 / d
  let y := p * (x + d) / m
  let z := p * (x + e) / m
  change 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z
  obtain ⟨hm3, hmltp, _, _, hmx, _⟩ :=
    certificate_modulus_facts p x hp hp4 hpx hxp
  change 3 ≤ m at hm3
  change m < p at hmltp
  change Nat.Coprime m x at hmx
  have hmpos : 0 < m := by omega
  have hpPos : 0 < p := hp.pos
  have hde : d * e = x ^ 2 := Nat.mul_div_cancel' hdvd
  obtain ⟨hdy, hdz⟩ := certificate_II_divisibility p x d e m hmx hde hdiv
  have hyEq : m * y = p * (x + d) := Nat.mul_div_cancel' hdy
  have hzEq : m * z = p * (x + e) := Nat.mul_div_cancel' hdz
  have hxy : x < y := by
    apply Nat.lt_of_mul_lt_mul_left (a := m)
    rw [hyEq]
    have hlt : m * x < p * x := Nat.mul_lt_mul_of_pos_right hmltp hx
    nlinarith
  have hxe : x < e := by
    by_contra h
    have hex : e ≤ x := by omega
    have hle : d * e ≤ d * x := Nat.mul_le_mul_left d hex
    have hlt : d * x < x * x := Nat.mul_lt_mul_of_pos_right hdx hx
    nlinarith [hde]
  have hyz : y < z := by
    apply Nat.lt_of_mul_lt_mul_left (a := m)
    rw [hyEq, hzEq]
    exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_left (lt_trans hdx hxe) x) hpPos
  refine ⟨by omega, hxy, hyz, ?_⟩
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hpPos
  have hxQ : (0 : ℚ) < x := by exact_mod_cast hx
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  have hd0 : (d : ℚ) ≠ 0 := ne_of_gt hdQ
  have hmQ : (m : ℚ) = 4 * (x : ℚ) - p := by
    dsimp only [m]
    rw [Nat.cast_sub (by omega : p ≤ 4 * x)]
    push_cast
    rfl
  have heQ : (e : ℚ) = (x : ℚ) ^ 2 / d := by
    dsimp only [e]
    rw [Nat.cast_div hdvd hd0, Nat.cast_pow]
  have hyQ : (y : ℚ) = (p : ℚ) * (x + d) / m := by
    dsimp only [y]
    rw [Nat.cast_div hdy hm0]
    push_cast
    rfl
  have hzQ : (z : ℚ) = (p : ℚ) * (x + e) / m := by
    dsimp only [z]
    rw [Nat.cast_div hdz hm0]
    push_cast
    rfl
  rw [hyQ, hzQ, heQ]
  exact certificate_II_identity (p : ℚ) x d m hpQ hxQ hdQ hmQ

/-- Certificate II: `d < x` and `m ∣ x+d` suffice for `Distinct p`. -/
theorem certificate_II (p x d : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hx : 0 < x) (hd : 0 < d) (hpx : p < 4 * x) (hxp : 2 * x < p)
    (hdvd : d ∣ x ^ 2) (hdx : d < x) (hdiv : (4 * x - p) ∣ x + d) : Distinct p := by
  exact ⟨x, p * (x + d) / (4 * x - p), p * (x + x ^ 2 / d) / (4 * x - p),
    certificate_II_witnesses p x d hp hp4 hx hd hpx hxp hdvd hdx hdiv⟩

end Erdos242Aux
