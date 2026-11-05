import Submission.FullSquareAxis
import Submission.CoveringGap

/-!
# Sharp offset bound for the full Type-II classification

For an eligible first denominator of a prime, the Type-II condition
`0<d<x`, `d∣x²`, `4x-p∣x+d` actually forces `4d<p`. This makes the
size assumption of the full square-divisor modular axis *necessary*
for all genuine Type-II certificates, not just a sufficient convenience.
It does not prove that a Type-II certificate always exists.
`Submission/Spec.lean` is neither imported nor modified.
-/

namespace Erdos242

/-- Coprimality of the first denominator and its modulus for an eligible
prime first denominator. -/
private theorem eligible_prime_coprime (p x : ℕ) (hp : p.Prime)
    (hlo : p < 4 * x) (hhi : 2 * x < p) :
    (4 * x - p).Coprime x := by
  let a := 4 * x - p
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hx : 0 < x := by omega
  have hxltp : x < p := by omega
  apply Nat.coprime_of_dvd
  intro q hq hqa hqx
  have hq4x : q ∣ 4 * x := hqx.mul_left 4
  have hqp : q ∣ p := by
    have hqap : q ∣ a + p := by rw [haeq]; exact hq4x
    exact (Nat.dvd_add_iff_left hqa).mpr (by simpa only [add_comm] using hqap)
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  exact (Nat.not_dvd_of_pos_of_lt hx hxltp) (heq ▸ hqx)

/-- A Type-II square-divisor `d` is *always below* `p/4`. The proof
uses the complementary divisor `b=x²/d` and its same target class:
`a=4x-p` divides both `x+d` and `x+b`, so `a` divides `b-d`.
If `4d≥p`, then `a≥4(x-d)` but `b-d<3(x-d)` because `2x<p≤4d`.
Primality ensures the cancellation `gcd(a,d)=1`. -/
theorem typeII_offset_lt_quarter (p x d : ℕ) (hp : p.Prime)
    (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hd : 0 < d) (hdx : d < x) (hdsq : d ∣ x ^ 2)
    (hadiv : 4 * x - p ∣ x + d) : 4 * d < p := by
  let a := 4 * x - p
  let b := x ^ 2 / d
  have ha : 0 < a := by dsimp [a]; omega
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hax : a.Coprime x := eligible_prime_coprime p x hp hlo hhi
  have had : a.Coprime d := (hax.pow_right 2).of_dvd_right hdsq
  have hdb : d * b = x ^ 2 := Nat.mul_div_cancel' hdsq
  have hbx : x < b := by
    by_contra ht
    have hle : b ≤ x := by omega
    have hble : d * b ≤ d * x := Nat.mul_le_mul_left d hle
    have hdxlt : d * x < x * x := Nat.mul_lt_mul_of_pos_right hdx (by omega)
    nlinarith only [hdb, hble, hdxlt]
  have habdiv : a ∣ x + b := by
    have heq : d * (x + b) = x * (x + d) := by nlinarith only [hdb]
    have hmul : a ∣ d * (x + b) := by rw [heq]; exact hadiv.mul_left x
    exact had.dvd_of_dvd_mul_left hmul
  by_contra hnot
  have hp_le : p ≤ 4 * d := by omega
  let r := x - d
  let q := b - d
  have hr : 0 < r := by dsimp [r]; omega
  have hrx : x = d + r := by dsimp [r]; omega
  have hqb : b = d + q := by dsimp [q]; omega
  have hq : 0 < q := by dsimp [q]; omega
  have haq : a ∣ q := by
    have hxsum : x + b = (x + d) + q := by omega
    rw [hxsum] at habdiv
    exact (Nat.dvd_add_iff_right hadiv).mpr habdiv
  have ha_le_q : a ≤ q := Nat.le_of_dvd hq haq
  have hr_eq : d * q = r * (x + d) := by
    rw [hrx, hqb] at hdb
    rw [hrx]
    nlinarith only [hdb]
  have hlt : x + d < 3 * d := by omega
  have hq_lt : q < 3 * r := by
    apply (Nat.mul_lt_mul_left hd).mp
    calc
      d * q = r * (x + d) := hr_eq
      _ < r * (3 * d) := Nat.mul_lt_mul_of_pos_left hlt hr
      _ = d * (3 * r) := by ring
  have ha_ge : 4 * r ≤ a := by omega
  omega

/-- In the difficult prime class, every *genuine* Type-II witness gives
exactly the square-divisor modular witness from `FullSquareAxis` including
both size bounds. The reverse implication to an ordered solution is already
`full_square_axis_good`; neither implication asserts pointwise existence. -/
theorem full_square_axis_of_hard_typeII (p x : ℕ) (hp : p.Prime)
    (hp24 : p % 24 = 1) (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hII : TypeII p x) : FullSquareAxis p := by
  obtain ⟨d, hd, hdx, hdsq, hadiv⟩ := hII
  let m := (x + d) / (4 * x - p)
  obtain ⟨hm, hdm, _, hdiv, _⟩ :=
    typeII_modular_parameter p x d hp hlo hhi hd hdx hdsq hadiv
  have hsmall : 4 * d < p :=
    typeII_offset_lt_quarter p x d hp hlo hhi hd hdx hdsq hadiv
  exact ⟨m, d, hm, full_square_axis_bound p m d hp24 hm hsmall hdiv,
    hd, hdm, hsmall, hdiv⟩

/-- Any full square-divisor modular certificate actually yields the *full*
Type-II condition at an eligible first denominator. This direction needs no
primality and avoids extracting a Type-II branch from a generic `Good` proof. -/
theorem typeII_of_full_square_axis (p : ℕ) (hw : FullSquareAxis p) :
    ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeII p x := by
  obtain ⟨m, d, hm, _, hd, hdsq, hsmall, hdiv⟩ := hw
  let h := 4 * m - 1
  let a := (p + 4 * d) / h
  let x := (p * m + d) / h
  have hh : 0 < h := by dsimp [h]; omega
  have hfour : h + 1 = 4 * m := by dsimp [h]; omega
  have ha : h * a = p + 4 * d := Nat.mul_div_cancel' hdiv
  have hnum : h ∣ p * m + d := by
    have hadd : h ∣ p * m + d + h * d := by
      have heq : p * m + d + h * d = (p + 4 * d) * m := by
        calc
          p * m + d + h * d = p * m + (h + 1) * d := by ring
          _ = p * m + (4 * m) * d := by rw [hfour]
          _ = (p + 4 * d) * m := by ring
      rw [heq]
      exact dvd_mul_of_dvd_left hdiv m
    exact (Nat.dvd_add_iff_left (dvd_mul_right h d)).mpr hadd
  have hx : h * x = p * m + d := Nat.mul_div_cancel' hnum
  have heq : 4 * x = p + a := by
    apply Nat.eq_of_mul_eq_mul_left hh
    nlinarith only [ha, hx, hfour]
  have hapos : 0 < a := by
    have hpos : 0 < h * a := by rw [ha]; omega
    exact Nat.pos_of_mul_pos_left hpos
  have ha_lt_p : a < p := by
    have hh3 : 3 ≤ h := by dsimp [h]; omega
    have hbound : 3 * a ≤ h * a := Nat.mul_le_mul_right a hh3
    rw [ha] at hbound
    omega
  have hlo : p < 4 * x := by omega
  have hhi : 2 * x < p := by omega
  have hdx : d < x := by omega
  have ham : a * m = x + d := by
    apply Nat.eq_of_mul_eq_mul_left hh
    have hleft : h * (a * m) = (p + 4 * d) * m := by
      calc
        h * (a * m) = (h * a) * m := by ring
        _ = (p + 4 * d) * m := by rw [ha]
    have hright : h * (x + d) = p * m + d + h * d := by rw [mul_add, hx]
    rw [hleft, hright]
    calc
      (p + 4 * d) * m = p * m + (h + 1) * d := by rw [hfour]; ring
      _ = p * m + d + h * d := by ring
  have hdandsq : d ∣ (x + d) ^ 2 := by
    rw [← ham]
    simpa only [mul_pow] using hdsq.mul_left (a ^ 2)
  have hxsq : d ∣ x ^ 2 := by
    have hkey : x ^ 2 + d * (2 * x + d) = (x + d) ^ 2 := by ring
    have htotal : d ∣ x ^ 2 + d * (2 * x + d) := by
      rw [hkey]
      exact hdandsq
    exact (Nat.dvd_add_iff_left (dvd_mul_right d _)).mpr htotal
  have hadiv : 4 * x - p ∣ x + d := by
    have ha' : 4 * x - p = a := by omega
    rw [ha', ← ham]
    exact dvd_mul_right a m
  exact ⟨x, hlo, hhi, d, hd, hdx, hxsq, hadiv⟩

/-- On hard primes, the `m≤(p−1)/6`, `d∣m²`, `4d<p` modular alternative
is **exactly** the Type-II branch of the ordered classification. This is an
equivalence of certificate *forms*, not a universal existence theorem:
Type I remains essential as a fallback in the known covering equivalence. -/
theorem full_square_axis_iff_typeII (p : ℕ) (hp : p.Prime) (hp24 : p % 24 = 1) :
    FullSquareAxis p ↔
      ∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeII p x := by
  constructor
  · exact typeII_of_full_square_axis p
  · rintro ⟨x, hlo, hhi, hII⟩
    exact full_square_axis_of_hard_typeII p x hp hp24 hlo hhi hII

/-- An exact hard-prime dichotomy: Type I at some eligible first
denominator, **or** the full `d∣m²`, `4d<p` Type-II modular axis.
Nothing here proves that either disjunct exists for an arbitrary prime. -/
theorem good_iff_hard_typeI_or_full_square_axis (p : ℕ)
    (hp : p.Prime) (hp24 : p % 24 = 1) :
    Good p ↔
      (∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeI p x) ∨ FullSquareAxis p := by
  have hgt : 2 < p := by have := hp.two_le; omega
  rw [good_iff_ordered_divisors p hp hgt]
  constructor
  · rintro ⟨x, hlo, hhi, hcase⟩
    rcases hcase with hI | hII
    · exact Or.inl ⟨x, hlo, hhi, hI⟩
    · exact Or.inr (full_square_axis_of_hard_typeII p x hp hp24 hlo hhi hII)
  · rintro (⟨x, hlo, hhi, hI⟩ | hfull)
    · exact ⟨x, hlo, hhi, Or.inl hI⟩
    · obtain ⟨x, hlo, hhi, hII⟩ := (full_square_axis_iff_typeII p hp hp24).mp hfull
      exact ⟨x, hlo, hhi, Or.inr hII⟩

/-- The **unproved right-hand-side existence assertion** is now phrased
with precisely the bounded square-divisor modular Type-II alternative in
the question. This is a logical equivalence, **not** its proof. -/
theorem all_good_iff_typeI_or_full_square_axis :
    (∀ n : ℕ, 2 < n → Good n) ↔
      ∀ p : ℕ, p.Prime → p % 24 = 1 →
        (∃ x : ℕ, p < 4 * x ∧ 2 * x < p ∧ TypeI p x) ∨ FullSquareAxis p := by
  constructor
  · intro hall p hp hp24
    have hgt : 2 < p := by have := hp.two_le; omega
    exact (good_iff_hard_typeI_or_full_square_axis p hp hp24).mp (hall p hgt)
  · intro hcover
    apply good_of_hard_primes
    intro p hp hp24
    exact (good_iff_hard_typeI_or_full_square_axis p hp hp24).mpr (hcover p hp hp24)



end Erdos242
