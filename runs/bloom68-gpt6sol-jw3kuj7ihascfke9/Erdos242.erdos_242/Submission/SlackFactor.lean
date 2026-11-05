import Submission.EuclideanExchange
import Submission.ForcedFactorAudit

/-!
# The positive-slack factorization for ordered prime Erdős–Straus solutions

The auxiliary integer `A = 4*x*y - p*(x+y)` satisfies
`p² + 4*A = (4*x-p)*(4*y-p)` and, when the last denominator is a
multiple of `p`, divides `x*y`.  All size and integrality conditions are
kept explicitly: a factorization by itself is not a solution.

The full equivalence below does NOT prove that every hard prime has a
witness.  The quadratic-character obstruction later in this file rules
out every choice `A ∣ p-1`, and even any fixed bound on `A` uniformly
for hard primes.  `Submission.Spec` is not imported or modified.
-/

namespace Erdos242

/-- The exact `A`-certificate, with the size condition ensuring that
`z = p*(x*y/A)` exceeds `y`. -/
def OrderedSlack (p A : ℕ) : Prop :=
  ∃ x y : ℕ, 0 < A ∧ p < 4 * x ∧ 2 * x < p ∧ x < y ∧
    A < p * x ∧ A ∣ x * y ∧
    (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A

/-- The same certificate expressed entirely through factors of `p²+4A`.
The last condition, `4A < p(p+a)`, is exactly `y < z` after recovering
`x=(p+a)/4` and `y=(p+b)/4`. -/
def SlackFactors (p A : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < A ∧ a % 4 = 3 ∧ b % 4 = 3 ∧ a < b ∧ a < p ∧
    a * b = p ^ 2 + 4 * A ∧
    A ∣ ((p + a) * (p + b)) / 16 ∧ 4 * A < p * (p + a)

private theorem factor_eq_iff_linear (p x y A : ℕ)
    (hx : p < 4 * x) (hy : p < 4 * y) :
    (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A ↔
      4 * x * y = p * (x + y) + A := by
  let a := 4 * x - p
  let b := 4 * y - p
  have ha : a + p = 4 * x := by dsimp [a]; omega
  have hb : b + p = 4 * y := by dsimp [b]; omega
  have hproduct : a * b + p * (a + b) + p ^ 2 = 16 * x * y := by
    calc
      a * b + p * (a + b) + p ^ 2 = (a + p) * (b + p) := by ring
      _ = (4 * x) * (4 * y) := by rw [ha, hb]
      _ = 16 * x * y := by ring
  have hsum : p * (a + b + 2 * p) = p * (4 * (x + y)) := by
    congr 1
    omega
  change a * b = p ^ 2 + 4 * A ↔ 4 * x * y = p * (x + y) + A
  constructor <;> intro h <;> nlinarith only [h, hproduct, hsum]

/-- The stated factorization and divisibility criteria are exactly the
ordered `A`-certificates; no primality is needed for this conversion. -/
theorem slack_factors_iff_ordered (p A : ℕ) (hp4 : p % 4 = 1) :
    SlackFactors p A ↔ OrderedSlack p A := by
  constructor
  · rintro ⟨a, b, hA, ha4, hb4, hab, hap, hproduct, hdiv, hsmall⟩
    let x := (p + a) / 4
    let y := (p + b) / 4
    have hax : 4 * x = p + a :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by omega : (p + a) % 4 = 0))
    have hby : 4 * y = p + b :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by omega : (p + b) % 4 = 0))
    have ha : 0 < a := by have := Nat.mod_le a 4; omega
    have hlow : p < 4 * x := by omega
    have hhigh : 2 * x < p := by omega
    have hxy : x < y := by omega
    have hquot : ((p + a) * (p + b)) / 16 = x * y := by
      have h16 : (p + a) * (p + b) = 16 * (x * y) := by
        rw [← hax, ← hby]
        ring
      rw [h16]
      simp
    have hbound : A < p * x := by
      have hpax := congrArg (fun n : ℕ => p * n) hax
      nlinarith only [hsmall, hpax]
    have hfac : (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A := by
      have ha' : 4 * x - p = a := by omega
      have hb' : 4 * y - p = b := by omega
      rwa [ha', hb']
    exact ⟨x, y, hA, hlow, hhigh, hxy, hbound, hquot ▸ hdiv, hfac⟩
  · rintro ⟨x, y, hA, hlow, hhigh, hxy, hbound, hdiv, hfac⟩
    let a := 4 * x - p
    let b := 4 * y - p
    have hax : a + p = 4 * x := by dsimp [a]; omega
    have hby : b + p = 4 * y := by dsimp [b]; omega
    have ha4 : a % 4 = 3 := by dsimp [a]; omega
    have hb4 : b % 4 = 3 := by dsimp [b]; omega
    have hab : a < b := by dsimp [a, b]; omega
    have hap : a < p := by dsimp [a]; omega
    have h16 : (p + a) * (p + b) = 16 * (x * y) := by
      rw [add_comm p a, add_comm p b, hax, hby]
      ring
    have hquot : ((p + a) * (p + b)) / 16 = x * y := by
      rw [h16]
      simp
    have hsmall : 4 * A < p * (p + a) := by
      have hpax := congrArg (fun n : ℕ => p * n) hax
      nlinarith only [hbound, hpax]
    exact ⟨a, b, hA, ha4, hb4, hab, hap, hfac, hquot ▸ hdiv, hsmall⟩

private theorem fraction_iff_product (p x y z : ℕ)
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

/-- Every exact ordered `A`-certificate produces the advertised triple
`(x,y,p*(x*y/A))`, without assuming primality. -/
theorem good_of_ordered_slack (p A : ℕ) (hp : 0 < p)
    (h : OrderedSlack p A) : Good p := by
  obtain ⟨x, y, hA, hlow, _, hxy, hsmall, hdiv, hfactor⟩ := h
  obtain ⟨t, hAt⟩ := hdiv
  have hx : 0 < x := by omega
  have hy : 0 < y := by omega
  have ht : 0 < t := by
    by_contra hn
    have hzero : t = 0 := by omega
    rw [hzero, mul_zero] at hAt
    have hxypos : 0 < x * y := Nat.mul_pos hx hy
    omega
  let z := p * t
  have hyz : y < z := by
    apply (Nat.mul_lt_mul_left hA).mp
    calc
      A * y < (p * x) * y := Nat.mul_lt_mul_of_pos_right hsmall hy
      _ = A * z := by
        dsimp [z]
        calc
          (p * x) * y = p * (x * y) := by ring
          _ = p * (A * t) := by rw [hAt]
          _ = A * (p * t) := by ring
  have hrel : 4 * x * y = p * (x + y) + A :=
    (factor_eq_iff_linear p x y A hlow (by omega)).mp hfactor
  have hpoly : 4 * x * y * z = p * (x * y + x * z + y * z) := by
    dsimp [z]
    calc
      4 * x * y * (p * t) = p * t * (4 * x * y) := by ring
      _ = p * t * (p * (x + y) + A) := by rw [hrel]
      _ = p * (x * y + x * (p * t) + y * (p * t)) := by rw [hAt]; ring
  exact ⟨x, y, z, by omega, hxy, hyz,
    (fraction_iff_product p x y z hp hx hy (by omega)).mpr hpoly⟩

/-- Conversely, at a prime `p>2`, the ordered equation forces `p∣z`.
Writing `z=p*t`, the equation itself forces `t∣xy`; the resulting
`A=xy/t` is an exact certificate with `0<A<p*x`. -/
theorem ordered_slack_of_good (p : ℕ) (hpp : p.Prime) (hgt : 2 < p)
    (hg : Good p) : ∃ A : ℕ, OrderedSlack p A := by
  obtain ⟨x, y, z, hx, hxy, hyz, heq⟩ := hg
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hzpos : 0 < z := by omega
  obtain ⟨hlow, hhigh, ⟨t, hz⟩⟩ :=
    ordered_solution_bounds p x y z hpp hgt hxpos hxy hyz heq
  have htpos : 0 < t := by
    by_contra hn
    have hzero : t = 0 := by omega
    rw [hzero] at hz
    simp at hz
    omega
  have hpoly := (fraction_iff_product p x y z (by omega) hxpos hypos hzpos).mp heq
  have hpoly2 : 4 * x * y * t = x * y + p * t * (x + y) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < p)
    calc
      p * (4 * x * y * t) = 4 * x * y * z := by rw [hz]; ring
      _ = p * (x * y + x * z + y * z) := hpoly
      _ = p * (x * y + p * t * (x + y)) := by rw [hz]; ring
  have htdiv : t ∣ x * y := by
    have hwhole : t ∣ x * y + p * t * (x + y) := by
      rw [← hpoly2]
      exact ⟨4 * x * y, by ring⟩
    have hother : t ∣ p * t * (x + y) := ⟨p * (x + y), by ring⟩
    have hwhole' : t ∣ p * t * (x + y) + x * y := by
      simpa only [add_comm] using hwhole
    exact (Nat.dvd_add_iff_right hother).mpr hwhole'
  let A := x * y / t
  have hAt : A * t = x * y := by
    simpa only [mul_comm] using (Nat.mul_div_cancel' htdiv)
  have hApos : 0 < A := by
    by_contra hn
    have hzero : A = 0 := Nat.eq_zero_of_not_pos hn
    rw [hzero, zero_mul] at hAt
    have hxypos : 0 < x * y := Nat.mul_pos hxpos hypos
    omega
  have hrelmul : (4 * x * y) * t = (p * (x + y) + A) * t := by
    calc
      (4 * x * y) * t = 4 * x * y * t := by ring
      _ = x * y + p * t * (x + y) := hpoly2
      _ = (p * (x + y) + A) * t := by rw [← hAt]; ring
  have hrel : 4 * x * y = p * (x + y) + A :=
    Nat.eq_of_mul_eq_mul_right htpos hrelmul
  have hsmall : A < p * x := by
    apply (Nat.mul_lt_mul_right hypos).mp
    calc
      A * y < A * z := Nat.mul_lt_mul_of_pos_left hyz hApos
      _ = (p * x) * y := by
        rw [hz]
        calc
          A * (p * t) = p * (A * t) := by ring
          _ = p * (x * y) := by rw [hAt]
          _ = (p * x) * y := by ring
  have hfac : (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A :=
    (factor_eq_iff_linear p x y A hlow (by omega)).mpr hrel
  exact ⟨A, x, y, hApos, hlow, hhigh, hxy, hsmall, ⟨t, hAt.symm⟩, hfac⟩

/-- Exact reformulation of ordered prime solvability by a positive
integer slack. It is an equivalence, NOT an all-primes existence claim. -/
theorem good_iff_exists_ordered_slack (p : ℕ) (hpp : p.Prime) (hgt : 2 < p) :
    Good p ↔ ∃ A : ℕ, OrderedSlack p A := by
  constructor
  · exact ordered_slack_of_good p hpp hgt
  · rintro ⟨A, hA⟩
    exact good_of_ordered_slack p A (by omega) hA

/-- The factor formulation is also an exact equivalence at hard primes;
its existence, however, is the original unproved global assertion. -/
theorem good_iff_exists_slack_factors (p : ℕ) (hpp : p.Prime)
    (hp24 : p % 24 = 1) : Good p ↔ ∃ A : ℕ, SlackFactors p A := by
  rw [good_iff_exists_ordered_slack p hpp (by have := hpp.two_le; omega)]
  exact exists_congr (fun A => (slack_factors_iff_ordered p A (by omega)).symm)

/-- The prime-divisibility of `A` exactly detects whether the middle
factorization denominator is divisible by `p`. The first-denominator
range gives `0 < 4x-p < p`, so primality cancels that factor. -/
theorem slack_prime_dvd_iff_middle (p x y A : ℕ) (hpp : p.Prime)
    (hlo : p < 4 * x) (hhi : 2 * x < p) (hxy : x < y)
    (hfac : (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A) :
    p ∣ A ↔ p ∣ y := by
  have hrel : 4 * x * y = p * (x + y) + A :=
    (factor_eq_iff_linear p x y A hlo (by omega)).mp hfac
  have ha : (4 * x - p) + p = 4 * x := by omega
  have hay : (4 * x - p) * y = p * x + A := by
    nlinarith only [hrel, congrArg (fun n : ℕ => n * y) ha]
  have hapos : 0 < 4 * x - p := by omega
  have halt : 4 * x - p < p := by omega
  have hnot : ¬p ∣ 4 * x - p :=
    Nat.not_dvd_of_pos_of_lt hapos halt
  constructor
  · intro hpA
    have hpay : p ∣ (4 * x - p) * y := by
      rw [hay]
      exact dvd_add (dvd_mul_right p x) hpA
    exact ((hpp.dvd_mul).mp hpay).resolve_left hnot
  · intro hpy
    have hsum : p ∣ p * x + A := by
      rw [← hay]
      exact hpy.mul_left _
    exact (Nat.dvd_add_iff_right (dvd_mul_right p x)).mpr hsum

/-- In the non-`p`-divisible branch, the given auxiliary integer itself
is a divisor of the first denominator's square. This follows already
from `A|xy` and the hyperbola relation, before any character argument. -/
private theorem slack_divides_first_square (p x y A : ℕ) (hpp : p.Prime)
    (hlo : p < 4 * x) (hxy : x < y)
    (hdiv : A ∣ x * y)
    (hfac : (4 * x - p) * (4 * y - p) = p ^ 2 + 4 * A)
    (hnot : ¬p ∣ A) : A ∣ x ^ 2 := by
  have hrel : 4 * x * y = p * (x + y) + A :=
    (factor_eq_iff_linear p x y A hlo (by omega)).mp hfac
  have ha : (4 * x - p) + p = 4 * x := by omega
  have hay : (4 * x - p) * y = p * x + A := by
    nlinarith only [hrel, congrArg (fun n : ℕ => n * y) ha]
  have hid : (4 * x - p) * (x * y) = p * x ^ 2 + A * x := by
    calc
      (4 * x - p) * (x * y) = ((4 * x - p) * y) * x := by ring
      _ = (p * x + A) * x := by rw [hay]
      _ = p * x ^ 2 + A * x := by ring
  have hsum : A ∣ p * x ^ 2 + A * x := by
    rw [← hid]
    exact hdiv.mul_left _
  have hsum' : A ∣ A * x + p * x ^ 2 := by simpa only [add_comm] using hsum
  have hpx : A ∣ p * x ^ 2 :=
    (Nat.dvd_add_iff_right (dvd_mul_right A x)).mpr hsum'
  have hcop : A.Coprime p := ((hpp.coprime_iff_not_dvd).mpr hnot).symm
  exact hcop.dvd_of_dvd_mul_left hpx

/-- Reciprocity makes every Type-I *complementary* divisor `r=x²/c`
a nonresidue as well. Here the shifted-square test is exactly the
complete Type-I test, not an additional assumption about a factor. -/
theorem square_shift_jacobi_negative (p x r : ℕ)
    (hpp : p.Prime) (hp8 : p % 8 = 1)
    (hlo : p < 4 * x) (hhi : 2 * x < p)
    (hrdiv : r ∣ x ^ 2)
    (hshift : 4 * x - p ∣ p ^ 2 + 4 * r) :
    jacobiSym (r : ℤ) p = -1 := by
  let c := x ^ 2 / r
  have hrc : r * c = x ^ 2 := Nat.mul_div_cancel' hrdiv
  have hcr : c * r = x ^ 2 := by simpa only [mul_comm] using hrc
  have hcdiv : c ∣ x ^ 2 := by rw [← hcr]; exact dvd_mul_right c r
  have hp4 : p % 4 = 1 := by omega
  have htarget : 4 * x - p ∣ 4 * c + 1 :=
    (typeI_slack_iff_square_shift p x c r hpp hp4 hlo hhi hcr).mpr hshift
  have hJc := typeI_cofactor_jacobi_neg_one p x c hp8 hlo hcdiv htarget
  have hxpos : 0 < x := by omega
  have hxltp : x < p := by omega
  have hnotx : ¬p ∣ x := Nat.not_dvd_of_pos_of_lt hxpos hxltp
  have hcop : x.Coprime p := ((hpp.coprime_iff_not_dvd).mpr hnotx).symm
  have hcopZ : (x : ℤ).gcd p = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
  have hrcZ : (r : ℤ) * (c : ℤ) = (x : ℤ) ^ 2 := by exact_mod_cast hrc
  have hJprod : jacobiSym (r : ℤ) p * jacobiSym (c : ℤ) p = 1 := by
    calc
      jacobiSym (r : ℤ) p * jacobiSym (c : ℤ) p =
          jacobiSym ((r : ℤ) * (c : ℤ)) p := (jacobiSym.mul_left _ _ _).symm
      _ = jacobiSym ((x : ℤ) ^ 2) p := by rw [hrcZ]
      _ = 1 := jacobiSym.sq_one' hcopZ
  rw [hJc] at hJprod
  nlinarith only [hJprod]

/-- In the `A`-factor formulation, the full ordered Type-I branch has
`(A/p) = -1`; the only other possibility is that `p∣A`, the Type-II
branch. This is necessary, not sufficient to construct factors. -/
theorem ordered_slack_jacobi_or_prime (p A : ℕ) (hpp : p.Prime)
    (hp8 : p % 8 = 1) (hw : OrderedSlack p A) :
    p ∣ A ∨ jacobiSym (A : ℤ) p = -1 := by
  by_cases hnot : p ∣ A
  · exact Or.inl hnot
  · right
    obtain ⟨x, y, _, hlo, hhi, hxy, _, hdiv, hfac⟩ := hw
    have hAdiv : A ∣ x ^ 2 :=
      slack_divides_first_square p x y A hpp hlo hxy hdiv hfac hnot
    have hshift : 4 * x - p ∣ p ^ 2 + 4 * A := ⟨4 * y - p, hfac.symm⟩
    exact square_shift_jacobi_negative p x A hpp hp8 hlo hhi hAdiv hshift

/-- If `p∤A`, the slack is *exactly* the complementary divisor
`A=x²/c` of a full Type-I cofactor `c`. The same `x` as in the
factorization is retained. -/
theorem ordered_slack_typeI_data (p A : ℕ) (hpp : p.Prime)
    (hp4 : p % 4 = 1) (hw : OrderedSlack p A) (hnot : ¬p ∣ A) :
    ∃ x c : ℕ, p < 4 * x ∧ 2 * x < p ∧ 0 < c ∧
      A * c = x ^ 2 ∧ TypeI p x := by
  obtain ⟨x, y, _, hlo, hhi, hxy, _, hdiv, hfac⟩ := hw
  have hAdiv : A ∣ x ^ 2 :=
    slack_divides_first_square p x y A hpp hlo hxy hdiv hfac hnot
  let c := x ^ 2 / A
  have hAc : A * c = x ^ 2 := Nat.mul_div_cancel' hAdiv
  have hcpos : 0 < c := by
    by_contra hn
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hn
    rw [hc0, mul_zero] at hAc
    have hxpos : 0 < x := by omega
    have hsq : 0 < x ^ 2 := pow_pos hxpos 2
    omega
  have hcr : c * A = x ^ 2 := by simpa only [mul_comm] using hAc
  have hshift : 4 * x - p ∣ p ^ 2 + 4 * A := ⟨4 * y - p, hfac.symm⟩
  have htarget : 4 * x - p ∣ 4 * c + 1 :=
    (typeI_slack_iff_square_shift p x c A hpp hp4 hlo hhi hcr).mpr hshift
  have hcdiv : c ∣ x ^ 2 := ⟨A, hcr.symm⟩
  exact ⟨x, c, hlo, hhi, hcpos, hAc, ⟨c, hcpos, hcdiv, htarget⟩⟩

/-- If `p∣A`, then `A=p*d`, where `d` is *exactly* the full Type-II
square divisor at the same first denominator. In particular `0<d<x`.
The proof uses `p∣y` and cancels `p` in the two defining equations. -/
theorem ordered_slack_typeII_data (p A : ℕ) (hpp : p.Prime)
    (hw : OrderedSlack p A) (hpA : p ∣ A) :
    ∃ x d : ℕ, p < 4 * x ∧ 2 * x < p ∧ 0 < d ∧ d < x ∧
      A = p * d ∧ TypeII p x := by
  obtain ⟨x, y, hA, hlo, hhi, hxy, hsmall, hdiv, hfac⟩ := hw
  obtain ⟨d, hAd⟩ := hpA
  have hp : 0 < p := hpp.pos
  have hdpos : 0 < d := by
    by_contra hn
    have hdz : d = 0 := Nat.eq_zero_of_not_pos hn
    rw [hdz, mul_zero] at hAd
    omega
  have hdltx : d < x := by
    rw [hAd] at hsmall
    exact (Nat.mul_lt_mul_left hp).mp hsmall
  have hpy : p ∣ y :=
    (slack_prime_dvd_iff_middle p x y A hpp hlo hhi hxy hfac).mp ⟨d, hAd⟩
  obtain ⟨m, hym⟩ := hpy
  have hrel : 4 * x * y = p * (x + y) + A :=
    (factor_eq_iff_linear p x y A hlo (by omega)).mp hfac
  have ha : (4 * x - p) + p = 4 * x := by omega
  have hay : (4 * x - p) * y = p * x + A := by
    nlinarith only [hrel, congrArg (fun n : ℕ => n * y) ha]
  have hm : (4 * x - p) * m = x + d := by
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p * ((4 * x - p) * m) = (4 * x - p) * y := by rw [hym]; ring
      _ = p * x + A := hay
      _ = p * (x + d) := by rw [hAd]; ring
  have hdm : d ∣ x * m := by
    obtain ⟨v, hv⟩ := hdiv
    refine ⟨v, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp
    calc
      p * (x * m) = x * y := by rw [hym]; ring
      _ = A * v := hv
      _ = p * (d * v) := by rw [hAd]; ring
  have hid : (4 * x - p) * (x * m) = x ^ 2 + d * x := by
    calc
      (4 * x - p) * (x * m) = ((4 * x - p) * m) * x := by ring
      _ = (x + d) * x := by rw [hm]
      _ = x ^ 2 + d * x := by ring
  have hsum : d ∣ x ^ 2 + d * x := by
    rw [← hid]
    exact hdm.mul_left _
  have hsum' : d ∣ d * x + x ^ 2 := by simpa only [add_comm] using hsum
  have hdsq : d ∣ x ^ 2 :=
    (Nat.dvd_add_iff_right (dvd_mul_right d x)).mpr hsum'
  have htarget : 4 * x - p ∣ x + d := ⟨m, hm.symm⟩
  exact ⟨x, d, hlo, hhi, hdpos, hdltx, hAd,
    ⟨d, hdpos, hdltx, hdsq, htarget⟩⟩

/-- The ordering inequality gives an explicit *pointwise* finite
search range. The upper bound grows quadratically with `p`. -/
theorem ordered_slack_size_bound (p A : ℕ) (hw : OrderedSlack p A) :
    2 * A < p ^ 2 := by
  obtain ⟨x, y, _, _, hhigh, _, hsmall, _, _⟩ := hw
  have hp : 0 < p := by omega
  have hmul : p * (2 * x) < p * p := Nat.mul_lt_mul_of_pos_left hhigh hp
  nlinarith only [hmul, hsmall]

/-- For hard primes this is an *exact, finite* decision criterion, not a
proof that the finite search is always successful. -/
theorem good_iff_finite_slack_factors (p : ℕ)
    (hpp : p.Prime) (hp24 : p % 24 = 1) :
    Good p ↔ ∃ A : ℕ, 0 < A ∧ 2 * A < p ^ 2 ∧ SlackFactors p A := by
  rw [good_iff_exists_slack_factors p hpp hp24]
  apply exists_congr
  intro A
  constructor
  · intro hw
    have ho : OrderedSlack p A :=
      (slack_factors_iff_ordered p A (by omega)).mp hw
    rcases hw with ⟨a, b, hA, rest⟩
    exact ⟨hA, ordered_slack_size_bound p A ho, ⟨a, b, hA, rest⟩⟩
  · rintro ⟨_, _, hw⟩
    exact hw

/-- No *square* `A` can work at a hard prime, including squares
large enough to be multiples of `p`: the latter violate the size bound,
while all nonzero squares are Jacobi residues modulo `p`. -/
theorem hard_no_square_slack (p s : ℕ) (hpp : p.Prime)
    (hp24 : p % 24 = 1) : ¬ OrderedSlack p (s ^ 2) := by
  intro hw
  have hbound := ordered_slack_size_bound p (s ^ 2) hw
  have hspos : 0 < s := by
    obtain ⟨x, y, hA, _⟩ := hw
    by_contra hn
    have hs : s = 0 := Nat.eq_zero_of_not_pos hn
    simp [hs] at hA
  have hsltp : s < p := by
    by_contra hn
    have hle : p ≤ s := by omega
    have hsq : p ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left hle 2
    omega
  have hnot : ¬ p ∣ s := Nat.not_dvd_of_pos_of_lt hspos hsltp
  have hnot2 : ¬ p ∣ s ^ 2 := by
    intro h
    exact hnot (hpp.dvd_of_dvd_pow h)
  have hneg : jacobiSym ((s ^ 2 : ℕ) : ℤ) p = -1 :=
    (ordered_slack_jacobi_or_prime p (s ^ 2) hpp (by omega) hw).resolve_left hnot2
  have hcop : s.Coprime p := ((hpp.coprime_iff_not_dvd).mpr hnot).symm
  have hcopZ : (s : ℤ).gcd p = 1 := by
    simpa only [Int.gcd_natCast_natCast] using hcop.gcd_eq_one
  have hone : jacobiSym ((s ^ 2 : ℕ) : ℤ) p = 1 := by
    simpa only [Nat.cast_pow] using (jacobiSym.sq_one' hcopZ)
  omega

/-- For `p=24k+1`, every *positive* divisor of `p−1=24k` is a Jacobi
residue modulo `p`. The proof uses the existing prime-factor reciprocity
lemma; `p` need not itself be prime for this statement. -/
theorem hard_minus_one_divisor_jacobi_one (k A : ℕ)
    (hA : 0 < A) (hdiv : A ∣ 24 * k) :
    jacobiSym (A : ℤ) (24 * k + 1) = 1 := by
  induction A using Nat.strong_induction_on with
  | h A ih =>
    by_cases hOne : A = 1
    · subst A
      simp
    · obtain ⟨ell, hell, helld⟩ := Nat.exists_prime_and_dvd hOne
      obtain ⟨t, ht⟩ := helld
      have htpos : 0 < t := by
        by_contra hn
        have htzero : t = 0 := Nat.eq_zero_of_not_pos hn
        rw [htzero, mul_zero] at ht
        omega
      have htlt : t < A := by
        rw [ht]
        nlinarith [hell.one_lt]
      have htA : t ∣ A := ⟨ell, by rw [ht]; ring⟩
      have hellA : ell ∣ A := ⟨t, ht⟩
      have hJell := hard_minus_one_prime_factor_residue k ell hell
        (dvd_trans hellA hdiv)
      have hJt := ih t htlt htpos (dvd_trans htA hdiv)
      rw [ht, Nat.cast_mul, jacobiSym.mul_left, hJell, hJt, one_mul]

/-- Consequently **no** ordered certificate for a hard prime can use
`A ∣ p−1` (even though the factors of `p−1` are explicit). -/
theorem ordered_slack_not_dvd_pminusone (p A : ℕ)
    (hpp : p.Prime) (hp24 : p % 24 = 1)
    (hw : OrderedSlack p A) : ¬A ∣ p - 1 := by
  intro hdiv
  have hApos : 0 < A := by
    obtain ⟨x, y, hA, _⟩ := hw
    exact hA
  have hA_lt : A < p := by
    have hpos : 0 < p - 1 := by have := hpp.two_le; omega
    have hle := Nat.le_of_dvd hpos hdiv
    omega
  have hnot : ¬p ∣ A := Nat.not_dvd_of_pos_of_lt hApos hA_lt
  have h8 : p % 8 = 1 := by omega
  have hJneg : jacobiSym (A : ℤ) p = -1 :=
    (ordered_slack_jacobi_or_prime p A hpp h8 hw).resolve_left hnot
  have hform : p = 24 * (p / 24) + 1 := by omega
  have hminus : p - 1 = 24 * (p / 24) := by omega
  have hdiv' : A ∣ 24 * (p / 24) := by rwa [hminus] at hdiv
  have hJone : jacobiSym (A : ℤ) p = 1 := by
    rw [hform]
    exact hard_minus_one_divisor_jacobi_one (p / 24) A hApos hdiv'
  omega

/-- No **fixed** bound `B` on this positive auxiliary integer covers all
hard primes: Dirichlet produces arbitrarily large primes `p ≡ 1`
modulo `24·B!`, for which every `1≤A≤B` divides `p−1` and is excluded.
This does not rule out an unbounded explicit formula for `A(p)`. -/
theorem hard_primes_escape_bounded_slack (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 24 = 1 ∧
      ∀ A : ℕ, 0 < A → A ≤ B → ¬ OrderedSlack p A := by
  let L := 24 * B.factorial
  have hL : L ≠ 0 := by dsimp [L]; positivity
  obtain ⟨p, hpgt, hpp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := L) (a := 1) hL (by simp)
  have h24 : 24 ∣ L := by dsimp [L]; exact dvd_mul_right 24 _
  have hp24 : p % 24 = 1 := by
    have hc := Nat.ModEq.of_dvd h24 hmod
    simpa [Nat.ModEq] using hc
  refine ⟨p, hpgt, hpp, hp24, ?_⟩
  intro A hA hAB hw
  have hfact : A ∣ B.factorial := Nat.dvd_factorial hA hAB
  have hAL : A ∣ L := by dsimp [L]; exact dvd_mul_of_dvd_right hfact 24
  have hmodA := Nat.ModEq.of_dvd hAL hmod
  have hminus : A ∣ p - 1 :=
    (Nat.modEq_iff_dvd' (by have := hpp.two_le; omega : 1 ≤ p)).mp hmodA.symm
  exact (ordered_slack_not_dvd_pminusone p A hpp hp24 hw) hminus

/-- The exclusion is stated directly in the question's factor variables:
no `A∣p−1` satisfies *all* factor, size and divisibility conditions. -/
theorem hard_slack_factors_not_dvd_pminusone (p A : ℕ)
    (hpp : p.Prime) (hp24 : p % 24 = 1)
    (hdiv : A ∣ p - 1) : ¬SlackFactors p A := by
  intro hw
  exact (ordered_slack_not_dvd_pminusone p A hpp hp24
    ((slack_factors_iff_ordered p A (by omega)).mp hw)) hdiv

/-- In particular, the explicit factor condition cannot be met with
`A≤B` for all hard primes, however large the *fixed* bound `B` is. -/
theorem hard_primes_escape_bounded_slack_factors (B N : ℕ) :
    ∃ p : ℕ, N < p ∧ p.Prime ∧ p % 24 = 1 ∧
      ∀ A : ℕ, 0 < A → A ≤ B → ¬SlackFactors p A := by
  obtain ⟨p, hpgt, hpp, hp24, hno⟩ := hard_primes_escape_bounded_slack B N
  refine ⟨p, hpgt, hpp, hp24, ?_⟩
  intro A hA hAB hw
  exact hno A hA hAB ((slack_factors_iff_ordered p A (by omega)).mp hw)

/-- Exact *positive* factor certificates at the five stress primes. The
separate integer-only audit checks that the listed `A` is minimal at each
prime; these finite certificates do not imply all-prime coverage. -/
theorem slack_factors_73 : SlackFactors 73 7 := by
  refine ⟨11, 487, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem slack_factors_193 : SlackFactors 193 10 := by
  refine ⟨7, 5327, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem slack_factors_2521 : SlackFactors 2521 76 := by
  refine ⟨1583, 4015, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem slack_factors_66529 : SlackFactors 66529 19 := by
  refine ⟨6811, 649847, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

theorem slack_factors_18481 : SlackFactors 18481 38 := by
  refine ⟨5079, 67247, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- All five displayed factor certificates yield **strictly ordered**
solutions by the general factor-to-solution theorem. No unproved prime
assertion is needed to use this direction of the construction. -/
theorem slack_factor_samples_good :
    Good 73 ∧ Good 193 ∧ Good 2521 ∧ Good 66529 ∧ Good 18481 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact good_of_ordered_slack 73 7 (by norm_num)
      ((slack_factors_iff_ordered 73 7 (by norm_num)).mp slack_factors_73)
  · exact good_of_ordered_slack 193 10 (by norm_num)
      ((slack_factors_iff_ordered 193 10 (by norm_num)).mp slack_factors_193)
  · exact good_of_ordered_slack 2521 76 (by norm_num)
      ((slack_factors_iff_ordered 2521 76 (by norm_num)).mp slack_factors_2521)
  · exact good_of_ordered_slack 66529 19 (by norm_num)
      ((slack_factors_iff_ordered 66529 19 (by norm_num)).mp slack_factors_66529)
  · exact good_of_ordered_slack 18481 38 (by norm_num)
      ((slack_factors_iff_ordered 18481 38 (by norm_num)).mp slack_factors_18481)

/-- A precise guard against omitting `A<p*x`: the factors and divisibility
hold at `p=73,A=32193`, but the resulting `z=146` is *less* than `y=3066`. -/
theorem factor_and_divisibility_do_not_force_order :
    11 * 12191 = 73 ^ 2 + 4 * 32193 ∧
      11 % 4 = 3 ∧ 12191 % 4 = 3 ∧ 11 < 12191 ∧
      (32193 ∣ 21 * 3066) ∧
      73 * ((21 * 3066) / 32193) = 146 ∧ 146 < 3066 ∧
      ¬32193 < 73 * 21 := by norm_num

end Erdos242
