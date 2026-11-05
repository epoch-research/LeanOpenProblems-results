import Submission.Arithmetic

/-!
# Actual natural unit-gap seeds

This file proves seed **existence**, not injectivity, a matching, a Hall bound,
or `S(N) = o(N)`. All labels below are maxima/cofactors of actual roots of
unit-gap comparisons. The target cutoff is the original `N`, not a lifted one.

A clean source means that neither root has a repeated greatest prime factor.
For roots at least two this is equivalent to strict cofactor smoothness.
The Euclidean branch uses `b < p`; the complementary branch uses `p ≤ b`.
Their auxiliary multipliers `u` are natural numbers, and are never assumed or
concluded to be prime. The target's other root is allowed to be dirty.

The only import is `Submission.Arithmetic`. Every declaration has an axiom
audit at the end of the file.
-/

namespace Erdos371.UnitGap

/-- A root is clean when its greatest prime factor occurs only once. -/
def CleanRoot (m : ℕ) : Prop := ¬ (Nat.maxPrimeFac m) ^ 2 ∣ m

/-- Both actual roots of the source comparison are clean. -/
def CleanComparison (n : ℕ) : Prop := CleanRoot n ∧ CleanRoot (n + 1)

/-- An actual maximum of one of the two roots, not a formal prime label. -/
def HasActualPrime (n p : ℕ) : Prop :=
  Nat.maxPrimeFac n = p ∨ Nat.maxPrimeFac (n + 1) = p

/-- An actual cofactor of one of the two roots. -/
def HasActualCofactor (n k : ℕ) : Prop := cofactor n = k ∨ cofactor (n + 1) = k

/-- Sharing a maximum label and sharing a cofactor label are distinct relations. -/
def SharesActualPrime (n t : ℕ) : Prop :=
  ∃ p : ℕ, HasActualPrime n p ∧ HasActualPrime t p

/-- No formal product cofactor is used in this relation. -/
def SharesActualCofactor (n t : ℕ) : Prop :=
  ∃ k : ℕ, HasActualCofactor n k ∧ HasActualCofactor t k

/-- An opposite-sign unit-gap seed in the original comparison prefix `[2,N]`.
This definition places no cleanliness restriction on the target. -/
def IsSeed (N n t : ℕ) : Prop :=
  2 ≤ t ∧ t ≤ N ∧ comparisonSign t = -comparisonSign n ∧
    (SharesActualPrime n t ∨ SharesActualCofactor n t)

/-- Cleanliness is exactly the strict smoothness test on the actual cofactor. -/
theorem cleanRoot_iff_cofactor_max_lt {m : ℕ} (hm : 2 ≤ m) :
    CleanRoot m ↔ Nat.maxPrimeFac (cofactor m) < Nat.maxPrimeFac m := by
  constructor
  · intro hclean
    apply lt_of_le_of_ne (maxPrimeFac_cofactor_le (by omega))
    intro heq
    apply hclean
    have hd : Nat.maxPrimeFac m ∣ cofactor m := by
      simpa only [heq] using (Nat.maxPrimeFac_dvd (n := cofactor m))
    have hsquare : (Nat.maxPrimeFac m) ^ 2 ∣ cofactor m * Nat.maxPrimeFac m := by
      rw [pow_two]
      exact mul_dvd_mul hd (dvd_refl _)
    simpa only [cofactor_mul_maxPrimeFac] using hsquare
  · intro hstrict hrep
    have heq := (repeated_max_firstCenter hm hrep).2.1
    omega

/-- The actual clean-source condition is precisely the two original strict
smoothness tests. No condition on a future quotient or refactored target is added. -/
theorem cleanComparison_iff_strict_smoothness {n : ℕ} (hn : 2 ≤ n) :
    CleanComparison n ↔
      Nat.maxPrimeFac (cofactor n) < Nat.maxPrimeFac n ∧
      Nat.maxPrimeFac (cofactor (n + 1)) < Nat.maxPrimeFac (n + 1) := by
  exact and_congr (cleanRoot_iff_cofactor_max_lt hn)
    (cleanRoot_iff_cofactor_max_lt (by omega : 2 ≤ n + 1))

/-- For a clean root at least three, its actual greatest prime is at least three.
Thus the lower endpoint `2` for a negative-source seed is not lost. -/
theorem clean_maxPrimeFac_ge_three {m : ℕ} (hm : 3 ≤ m) (hclean : CleanRoot m) :
    3 ≤ Nat.maxPrimeFac m := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
  have hstrict := (cleanRoot_iff_cofactor_max_lt (by omega : 2 ≤ m)).mp hclean
  have hcpos := cofactor_pos (by omega : 0 < m)
  by_contra h
  have hp2 : Nat.maxPrimeFac m = 2 := by have := hp.two_le; omega
  have hc1 : cofactor m = 1 := by
    by_contra hc
    have hcp := Nat.prime_maxPrimeFac_of_one_lt (cofactor m) (by omega)
    have := hcp.two_le
    omega
  have hrec := cofactor_mul_maxPrimeFac m
  rw [hc1, hp2, one_mul] at hrec
  omega

/-- A legal actual row cell retains its actual cofactor, also at the first cell. -/
theorem actual_row_cell {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hkp : Nat.maxPrimeFac k ≤ p) :
    Nat.maxPrimeFac (k * p) = p ∧ cofactor (k * p) = k := by
  have hm : Nat.maxPrimeFac (k * p) = p := by
    rw [maxPrimeFac_mul_of_pos hk hp.pos, hp.maxPrimeFac_eq_self, max_eq_right hkp]
  exact ⟨hm, by simp only [cofactor, hm]; exact Nat.mul_div_cancel k hp.pos⟩

/-- Strict source smoothness certifies a clean actual row cell. -/
theorem strict_row_cell {k p : ℕ} (hk : 0 < k) (hp : p.Prime)
    (hkp : Nat.maxPrimeFac k < p) :
    Nat.maxPrimeFac (k * p) = p ∧ cofactor (k * p) = k ∧ CleanRoot (k * p) := by
  have hrow := actual_row_cell hk hp hkp.le
  have hple : p ≤ k * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p (by omega : 1 ≤ k)
  refine ⟨hrow.1, hrow.2, ?_⟩
  apply (cleanRoot_iff_cofactor_max_lt (hp.two_le.trans hple)).mpr
  simpa only [hrow.1, hrow.2] using hkp

/- ## Exact Euclidean normalizations (`2 ≤ b < p`)
The quotients `u` in both orientations may be composite. -/

/-- Normalize `ap+1=bq` by dividing `a` by `b`, with all bounds explicit. -/
theorem euclidean_plus_normalize {a b p q : ℕ} (hb : 2 ≤ b) (hba : b < a)
    (hp : 3 ≤ p) (_hbp : b < p) (heq : a * p + 1 = b * q) :
    let r := a % b
    let h := a / b
    let u := (r * p + 1) / b
    0 < r ∧ r < b ∧ 0 < h ∧ 0 < u ∧ u < p ∧
      a = r + h * b ∧ r * p + 1 = b * u ∧ q = u + h * p := by
  dsimp only
  have hb0 : 0 < b := by omega
  have hd : b ∣ a * p + 1 := ⟨q, heq⟩
  have hdseed : b ∣ (a % b) * p + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hd
  have hr : 0 < a % b := by
    by_contra h
    have hz : a % b = 0 := by omega
    have hb1 : b = 1 := Nat.dvd_one.mp (by simpa [hz] using hdseed)
    omega
  have hrb : a % b < b := Nat.mod_lt _ hb0
  have hh : 0 < a / b := Nat.div_pos hba.le hb0
  have hseed : (a % b) * p + 1 = b * (((a % b) * p + 1) / b) :=
    (Nat.mul_div_cancel' hdseed).symm
  have hu : 0 < ((a % b) * p + 1) / b := by
    by_contra h
    have hz : ((a % b) * p + 1) / b = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hseed
  have hmul : (a % b) * p + p ≤ b * p := by
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using
      Nat.mul_le_mul_right p (Nat.succ_le_of_lt hrb)
  have hup : ((a % b) * p + 1) / b < p := by
    by_contra h
    have hle := Nat.mul_le_mul_left b (by omega : p ≤ ((a % b) * p + 1) / b)
    omega
  have hadec : a = a % b + (a / b) * b := by
    simpa only [mul_comm] using (Nat.mod_add_div a b).symm
  have hsource : (a % b + (a / b) * b) * p + 1 = b * q := by
    rwa [← hadec]
  have hqeq : q * b = (((a % b) * p + 1) / b + (a / b) * p) * b := by
    nlinarith [hsource, hseed]
  exact ⟨hr, hrb, hh, hu, hup, hadec, hseed, Nat.eq_of_mul_eq_mul_right hb0 hqeq⟩

/-- Normalize `bq+1=ap` in the other orientation. -/
theorem euclidean_minus_normalize {a b p q : ℕ} (hb : 2 ≤ b) (hba : b < a)
    (hp : 3 ≤ p) (_hbp : b < p) (heq : b * q + 1 = a * p) :
    let r := a % b
    let h := a / b
    let u := (r * p) / b
    0 < r ∧ r < b ∧ 0 < h ∧ 0 < u ∧ u < p ∧
      a = r + h * b ∧ b * u + 1 = r * p ∧ q = u + h * p := by
  dsimp only
  have hb0 : 0 < b := by omega
  have hmod : (a * p) % b = 1 := by
    rw [← heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < b)]
  have hrmod : ((a % b) * p) % b = 1 := by
    simpa only [Nat.mul_mod, Nat.mod_mod] using hmod
  have hr : 0 < a % b := by
    by_contra h
    have hz : a % b = 0 := by omega
    simp [hz] at hrmod
  have hrb : a % b < b := Nat.mod_lt _ hb0
  have hh : 0 < a / b := Nat.div_pos hba.le hb0
  have hseed : b * (((a % b) * p) / b) + 1 = (a % b) * p := by
    simpa only [hrmod, add_comm] using Nat.mod_add_div ((a % b) * p) b
  have hple : p ≤ (a % b) * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p (by omega : 1 ≤ a % b)
  have hu : 0 < ((a % b) * p) / b := by
    by_contra h
    have hz : ((a % b) * p) / b = 0 := Nat.eq_zero_of_not_pos h
    simp only [hz, mul_zero, zero_add] at hseed
    omega
  have hmul : (a % b) * p + p ≤ b * p := by
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using
      Nat.mul_le_mul_right p (Nat.succ_le_of_lt hrb)
  have hup : ((a % b) * p) / b < p := by
    by_contra h
    have hle := Nat.mul_le_mul_left b (by omega : p ≤ ((a % b) * p) / b)
    omega
  have hadec : a = a % b + (a / b) * b := by
    simpa only [mul_comm] using (Nat.mod_add_div a b).symm
  have hsource : b * q + 1 = (a % b + (a / b) * b) * p := by
    rwa [← hadec]
  have hqeq : q * b = (((a % b) * p) / b + (a / b) * p) * b := by
    nlinarith [hsource, hseed]
  exact ⟨hr, hrb, hh, hu, hup, hadec, hseed, Nat.eq_of_mul_eq_mul_right hb0 hqeq⟩

/- ## Exact complementary normalizations (`p ≤ b`)
These retain the larger *actual* prime `q`, even if the other root is refactored. -/

/-- Normalize a positive source by dividing `b` by `p`. -/
theorem complement_plus_normalize {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (_hpq : p < q) (hb : p ≤ b) (heq : a * p + 1 = b * q) :
    let r := b % p
    let h := b / p
    let u := (r * q) / p
    0 < r ∧ r < p ∧ 0 < h ∧ 0 < u ∧ u < q ∧
      b = r + h * p ∧ r * q = p * u + 1 ∧ a = u + h * q := by
  dsimp only
  have hmod : (b * q) % p = 1 := by
    rw [← heq]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt]
  have hrmod : ((b % p) * q) % p = 1 := by
    simpa only [Nat.mul_mod, Nat.mod_mod] using hmod
  have hr : 0 < b % p := by
    by_contra h
    have hz : b % p = 0 := by omega
    simp [hz] at hrmod
  have hrp : b % p < p := Nat.mod_lt _ hp.pos
  have hh : 0 < b / p := Nat.div_pos hb hp.pos
  have hdet : (b % p) * q = p * (((b % p) * q) / p) + 1 := by
    simpa only [hrmod, add_comm] using (Nat.mod_add_div ((b % p) * q) p).symm
  have hqle : q ≤ (b % p) * q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q (by omega : 1 ≤ b % p)
  have hu : 0 < ((b % p) * q) / p := by
    by_contra h
    have hz : ((b % p) * q) / p = 0 := Nat.eq_zero_of_not_pos h
    have := hq.two_le
    simp only [hz, mul_zero, zero_add] at hdet
    omega
  have huq : ((b % p) * q) / p < q := by
    apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
    simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_right hrp hq.pos
  have hbdec : b = b % p + (b / p) * p := by
    simpa only [mul_comm] using (Nat.mod_add_div b p).symm
  have hsource : a * p + 1 = (b % p + (b / p) * p) * q := by
    rwa [← hbdec]
  have haeq : a * p = (((b % p) * q) / p + (b / p) * q) * p := by
    nlinarith [hsource, hdet]
  exact ⟨hr, hrp, hh, hu, huq, hbdec, hdet, Nat.eq_of_mul_eq_mul_right hp.pos haeq⟩

/-- Normalize a negative source by the same division, with the opposite determinant. -/
theorem complement_minus_normalize {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (_hpq : p < q) (hb : p ≤ b) (heq : b * q + 1 = a * p) :
    let r := b % p
    let h := b / p
    let u := (r * q + 1) / p
    0 < r ∧ r < p ∧ 0 < h ∧ 0 < u ∧ u < q ∧
      b = r + h * p ∧ r * q + 1 = p * u ∧ a = u + h * q := by
  dsimp only
  have hd : p ∣ b * q + 1 := ⟨a, by simpa only [mul_comm] using heq⟩
  have hdseed : p ∣ (b % p) * q + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod] using Nat.mod_eq_zero_of_dvd hd
  have hr : 0 < b % p := by
    by_contra h
    have hz : b % p = 0 := by omega
    have hp1 : p = 1 := Nat.dvd_one.mp (by simpa [hz] using hdseed)
    have := hp.one_lt
    omega
  have hrp : b % p < p := Nat.mod_lt _ hp.pos
  have hh : 0 < b / p := Nat.div_pos hb hp.pos
  have hdet : (b % p) * q + 1 = p * (((b % p) * q + 1) / p) :=
    (Nat.mul_div_cancel' hdseed).symm
  have hu : 0 < ((b % p) * q + 1) / p := by
    by_contra h
    have hz : ((b % p) * q + 1) / p = 0 := Nat.eq_zero_of_not_pos h
    simp [hz] at hdet
  have hmul : (b % p) * q + q ≤ p * q := by
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] using
      Nat.mul_le_mul_right q (Nat.succ_le_of_lt hrp)
  have huq : ((b % p) * q + 1) / p < q := by
    apply (Nat.div_lt_iff_lt_mul hp.pos).mpr
    have := hq.two_le
    have hlt : (b % p) * q + 1 < p * q := by omega
    simpa only [mul_comm] using hlt
  have hbdec : b = b % p + (b / p) * p := by
    simpa only [mul_comm] using (Nat.mod_add_div b p).symm
  have hsource : (b % p + (b / p) * p) * q + 1 = a * p := by
    rwa [← hbdec]
  have haeq : a * p = (((b % p) * q + 1) / p + (b / p) * q) * p := by
    nlinarith [hsource, hdet]
  exact ⟨hr, hrp, hh, hu, huq, hbdec, hdet, Nat.eq_of_mul_eq_mul_right hp.pos haeq⟩

/- ## Primitive complements and certified noncenter targets -/

/-- A positive primitive determinant has an actual negative complement.
There is deliberately no primality assumption on `u`. -/
theorem complement_plus_seed {p q r u : ℕ} (hq : q.Prime)
    (hpq : p < q) (hr : 0 < r) (hrp : r < p)
    (huq : u < q) (hdet : r * q = p * u + 1) :
    (p - r) * q + 1 = p * (q - u) ∧
      Nat.maxPrimeFac ((p - r) * q) = q ∧
      Nat.maxPrimeFac ((p - r) * q + 1) < q ∧
      comparisonSign ((p - r) * q) = -1 := by
  have hc : 0 < p - r := by omega
  have hcp : p - r < p := by omega
  have hcomp : (p - r) * q + 1 = p * (q - u) := by
    nlinarith [Nat.sub_add_cancel hrp.le, Nat.sub_add_cancel huq.le]
  have hmax := euclidean_plus_seed hq hc hcp hpq hcomp
  exact ⟨hcomp, hmax.1, hmax.2, euclidean_plus_seed_sign hq hc hcp hpq hcomp⟩

/-- A negative primitive determinant has an actual positive complement.
Refactoring the other root cannot change the retained actual maximum `q`. -/
theorem complement_minus_seed {p q r u : ℕ} (hq : q.Prime)
    (hpq : p < q) (hr : 0 < r) (hrp : r < p)
    (huq : u < q) (hdet : r * q + 1 = p * u) :
    p * (q - u) + 1 = (p - r) * q ∧
      Nat.maxPrimeFac ((p - r) * q - 1) < q ∧
      Nat.maxPrimeFac ((p - r) * q - 1 + 1) = q ∧
      comparisonSign ((p - r) * q - 1) = 1 := by
  have hc : 0 < p - r := by omega
  have hcp : p - r < p := by omega
  have hcomp : p * (q - u) + 1 = (p - r) * q := by
    nlinarith [Nat.sub_add_cancel hrp.le, Nat.sub_add_cancel huq.le]
  have hmax := euclidean_minus_seed hq hc hcp hpq hcomp
  have ht : p * (q - u) = (p - r) * q - 1 := by omega
  have hs := euclidean_minus_seed_sign hq hc hcp hpq hcomp
  rw [ht] at hmax hs
  exact ⟨hcomp, hmax.1, hmax.2, hs⟩

/-- Both orientations of a complementary seed are strictly below their sources. -/
theorem complement_below_source {b p q r : ℕ} (hb : p ≤ b)
    (hq : 2 ≤ q) (hr : 0 < r) (hrp : r < p) :
    (p - r) * q < b * q - 1 ∧ (p - r) * q - 1 < b * q := by
  have hcb : p - r + 1 ≤ b := by omega
  have hm : (p - r) * q + q ≤ b * q := by
    simpa only [Nat.add_mul, one_mul] using Nat.mul_le_mul_right q hcb
  omega

/-- The explicit Euclidean target for `ap+1=bq` lies in `[2,ap)`.
Its high root is clean; no smoothness or primality of a hypothetical `u` is assumed. -/
theorem euclidean_plus_target {a b p q : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hb : 2 ≤ b) (hba : b < a) (hbp : b < p) (heq : a * p + 1 = b * q) :
    let t := (a % b) * p
    2 ≤ t ∧ t < a * p ∧ Nat.maxPrimeFac t = p ∧
      Nat.maxPrimeFac (t + 1) < p ∧ comparisonSign t = -1 ∧ CleanRoot t := by
  dsimp only
  obtain ⟨hr, hrb, _hh, _hu, _hup, _hadec, hseed, _hqeq⟩ :=
    euclidean_plus_normalize hb hba hp3 hbp heq
  have ht := euclidean_plus_seed hp hr hrb hbp hseed
  have hs := euclidean_plus_seed_sign hp hr hrb hbp hseed
  have hrow := strict_row_cell hr hp (Nat.maxPrimeFac_le.trans_lt (hrb.trans hbp))
  have hple : p ≤ (a % b) * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p (by omega : 1 ≤ a % b)
  exact ⟨by omega, Nat.mul_lt_mul_of_pos_right (hrb.trans hba) hp.pos,
    ht.1, ht.2, hs, hrow.2.2⟩

/-- The explicit Euclidean target for `bq+1=ap` lies in `[2,bq)`.
The endpoint `t=2` is allowed and its sign is an actual prime-factor comparison. -/
theorem euclidean_minus_target {a b p q : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hb : 2 ≤ b) (hba : b < a) (hbp : b < p) (heq : b * q + 1 = a * p) :
    let t := (a % b) * p - 1
    2 ≤ t ∧ t < b * q ∧ Nat.maxPrimeFac t < p ∧
      Nat.maxPrimeFac (t + 1) = p ∧ comparisonSign t = 1 ∧ CleanRoot (t + 1) := by
  dsimp only
  obtain ⟨hr, hrb, _hh, _hu, _hup, _hadec, hseed, _hqeq⟩ :=
    euclidean_minus_normalize hb hba hp3 hbp heq
  have ht := euclidean_minus_seed hp hr hrb hbp hseed
  have hs := euclidean_minus_seed_sign hp hr hrb hbp hseed
  have hminus : b * (((a % b) * p) / b) = (a % b) * p - 1 := by omega
  rw [hminus] at ht hs
  have hrow := strict_row_cell hr hp (Nat.maxPrimeFac_le.trans_lt (hrb.trans hbp))
  have hple : p ≤ (a % b) * p := by
    simpa only [one_mul] using Nat.mul_le_mul_right p (by omega : 1 ≤ a % b)
  have hlt : (a % b) * p < a * p := Nat.mul_lt_mul_of_pos_right (hrb.trans hba) hp.pos
  have hadd : (a % b) * p - 1 + 1 = (a % b) * p := by omega
  exact ⟨by omega, by omega, ht.1, ht.2, hs, hadd.symm ▸ hrow.2.2⟩

/-- The explicit complementary target for `ap+1=bq`, `p ≤ b`, lies in `[2,ap)`.
The retained maximum is the genuine larger source prime `q`. -/
theorem complement_plus_target {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hb : p ≤ b) (heq : a * p + 1 = b * q) :
    let t := (p - b % p) * q
    2 ≤ t ∧ t < a * p ∧ Nat.maxPrimeFac t = q ∧
      Nat.maxPrimeFac (t + 1) < q ∧ comparisonSign t = -1 ∧ CleanRoot t := by
  dsimp only
  obtain ⟨hr, hrp, _hh, _hu, huq, _hbdec, hdet, _haeq⟩ :=
    complement_plus_normalize hp hq hpq hb heq
  have ht := complement_plus_seed hq hpq hr hrp huq hdet
  have hc : 0 < p - b % p := by omega
  have hcp : p - b % p < p := by omega
  have hrow := strict_row_cell hc hq (Nat.maxPrimeFac_le.trans_lt (hcp.trans hpq))
  have hqle : q ≤ (p - b % p) * q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q (by omega : 1 ≤ p - b % p)
  have hbelow := complement_below_source hb hq.two_le hr hrp
  have hsource : a * p = b * q - 1 := by omega
  exact ⟨hq.two_le.trans hqle, by simpa only [← hsource] using hbelow.1,
    ht.2.1, ht.2.2.1, ht.2.2.2, hrow.2.2⟩

/-- The explicit complementary target for `bq+1=ap`, `p ≤ b`, lies in `[2,bq)`.
No formal divisor label is substituted for the actual maximum `q`. -/
theorem complement_minus_target {a b p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hb : p ≤ b) (heq : b * q + 1 = a * p) :
    let t := (p - b % p) * q - 1
    2 ≤ t ∧ t < b * q ∧ Nat.maxPrimeFac t < q ∧
      Nat.maxPrimeFac (t + 1) = q ∧ comparisonSign t = 1 ∧ CleanRoot (t + 1) := by
  dsimp only
  obtain ⟨hr, hrp, _hh, _hu, huq, _hbdec, hdet, _haeq⟩ :=
    complement_minus_normalize hp hq hpq hb heq
  have ht := complement_minus_seed hq hpq hr hrp huq hdet
  have hc : 0 < p - b % p := by omega
  have hcp : p - b % p < p := by omega
  have hrow := strict_row_cell hc hq (Nat.maxPrimeFac_le.trans_lt (hcp.trans hpq))
  have hqle : q ≤ (p - b % p) * q := by
    simpa only [one_mul] using Nat.mul_le_mul_right q (by omega : 1 ≤ p - b % p)
  have hp2 := hp.two_le
  have hbelow := complement_below_source hb hq.two_le hr hrp
  have hadd : (p - b % p) * q - 1 + 1 = (p - b % p) * q := by
    have := hq.two_le
    omega
  exact ⟨by omega, hbelow.2, ht.2.1, ht.2.2.1, ht.2.2.2, hadd.symm ▸ hrow.2.2⟩

/- ## Actual prime centers and the one terminal fallback -/

/-- At an odd prime center `q ≥ 3`, the incoming sign is positive and the
outgoing sign is negative. Both assertions concern actual adjacent roots. -/
theorem prime_center_signs {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    Nat.maxPrimeFac (q - 1) < q ∧ Nat.maxPrimeFac (q + 1) < q ∧
      comparisonSign (q - 1) = 1 ∧ comparisonSign q = -1 := by
  have hleft : Nat.maxPrimeFac (q - 1) < q := Nat.maxPrimeFac_le.trans_lt (by omega)
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  have hhalf2 : 2 ≤ (q + 1) / 2 := by omega
  have hhalfq : (q + 1) / 2 < q := by omega
  have hdouble : 2 * ((q + 1) / 2) = q + 1 := by omega
  have hright : Nat.maxPrimeFac (q + 1) < q := by
    rw [← hdouble, maxPrimeFac_double hhalf2]
    exact Nat.maxPrimeFac_le.trans_lt hhalfq
  have hprev : q - 1 + 1 = q := by omega
  have hsleft : comparisonSign (q - 1) = 1 := by
    simp only [comparisonSign, hprev, hq.maxPrimeFac_eq_self, if_pos hleft]
  have hsright : comparisonSign q = -1 := by
    apply (comparisonSign_eq_neg_one_iff _).mpr
    simpa only [hq.maxPrimeFac_eq_self] using hright
  exact ⟨hleft, hright, hsleft, hsright⟩

/-- The fixed fallback target has a negative sign and an actual cofactor one. -/
theorem fallback_three : comparisonSign 3 = -1 ∧ cofactor 3 = 1 := by
  exact ⟨(prime_center_signs Nat.prime_three (by omega)).2.2.2,
    (cofactor_eq_one_iff (by omega : 2 ≤ 3)).mpr Nat.prime_three⟩



/-- The positive prime-center rule uses `q` when it is in range; otherwise it
uses the actual cofactor-one target `3`. No prime retention is claimed for
that fallback. The source cutoff is exactly `q-1 ≤ N`. -/
theorem prime_center_forward_seed {N q : ℕ} (hN : 3 ≤ N) (hq : q.Prime)
    (hq3 : 3 ≤ q) (hcut : q - 1 ≤ N) :
    IsSeed N (q - 1) (if q ≤ N then q else 3) := by
  have hs := prime_center_signs hq hq3
  have hprev : q - 1 + 1 = q := by omega
  by_cases hqN : q ≤ N
  · rw [if_pos hqN]
    refine ⟨by omega, hqN, ?_, Or.inl ⟨q, ?_, ?_⟩⟩
    · rw [hs.2.2.1, hs.2.2.2]
    · exact Or.inr (by rw [hprev, hq.maxPrimeFac_eq_self])
    · exact Or.inl hq.maxPrimeFac_eq_self
  · rw [if_neg hqN]
    have hterminal : q = N + 1 := by omega
    have hsourcecof : cofactor (q - 1 + 1) = 1 := by
      rw [hprev, hterminal]
      exact (cofactor_eq_one_iff (by omega : 2 ≤ N + 1)).mpr (hterminal ▸ hq)
    refine ⟨by omega, hN, ?_, Or.inr ⟨1, Or.inr hsourcecof, Or.inl fallback_three.2⟩⟩
    rw [fallback_three.1, hs.2.2.1]

/-- A negative prime-center source always has the lower positive center in range. -/
theorem prime_center_backward_seed {N q : ℕ} (hq : q.Prime)
    (hq3 : 3 ≤ q) (hcut : q ≤ N) : IsSeed N q (q - 1) := by
  have hs := prime_center_signs hq hq3
  have hprev : q - 1 + 1 = q := by omega
  refine ⟨by omega, by omega, ?_, Or.inl ⟨q, Or.inl hq.maxPrimeFac_eq_self, ?_⟩⟩
  · rw [hs.2.2.1, hs.2.2.2]
    norm_num
  · exact Or.inr (by rw [hprev, hq.maxPrimeFac_eq_self])

/-- An explicit terminal statement: when the larger prime root is `N+1`, the
fallback is an actual cofactor-one edge entirely within `[2,N]`. -/
theorem terminal_prime_center_seed {N : ℕ} (hN : 3 ≤ N) (hq : (N + 1).Prime) :
    IsSeed N N 3 ∧ SharesActualCofactor N 3 := by
  have hs := prime_center_forward_seed hN hq (by omega) (by omega)
  have hseed : IsSeed N N 3 := by simpa only [Nat.add_sub_cancel, show ¬ N + 1 ≤ N by omega,
    if_false] using hs
  have hshare : SharesActualCofactor N 3 :=
    ⟨1, Or.inr ((cofactor_eq_one_iff (by omega : 2 ≤ N + 1)).mpr hq),
      Or.inl fallback_three.2⟩
  exact ⟨hseed, hshare⟩

/- ## Total deterministic rules, with the original cutoff -/

/-- Rule for a normalized positive source `ap+1=bq`.
The three cases are centers, Euclidean seeds, and complementary seeds. -/
def plusSeed (N a b p q : ℕ) : ℕ :=
  if b = 1 then (if q ≤ N then q else 3)
  else if b < p then (a % b) * p else (p - b % p) * q

/-- Rule for a normalized negative source `bq+1=ap`. -/
def minusSeed (a b p q : ℕ) : ℕ :=
  if b = 1 then q - 1
  else if b < p then (a % b) * p - 1 else (p - b % p) * q - 1

/-- The rule uses only actual root maxima and actual cofactors.
For positive sources `(a,b,p,q)=(c(n),c(n+1),P(n),P(n+1))`;
for negative sources their roles are reversed. It is a total natural function;
the correctness theorem below imposes the precise clean-prefix assumptions. -/
def unitGapSeed (N n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) then
    plusSeed N (cofactor n) (cofactor (n + 1))
      (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))
  else
    minusSeed (cofactor (n + 1)) (cofactor n)
      (Nat.maxPrimeFac (n + 1)) (Nat.maxPrimeFac n)

/-- All positive-source branches are legal actual seeds. Both strict source
smoothness tests and the original source cutoff are visible hypotheses. -/
theorem plusSeed_isSeed {N a b p q : ℕ} (hN : 3 ≤ N)
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hpq : p < q)
    (hb : 1 ≤ b) (hba : b < a)
    (hsa : Nat.maxPrimeFac a < p) (hsb : Nat.maxPrimeFac b < q)
    (heq : a * p + 1 = b * q) (hcut : a * p ≤ N) :
    IsSeed N (a * p) (plusSeed N a b p q) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hrowa := strict_row_cell ha0 hp hsa
  have hrowb := strict_row_cell hb0 hq hsb
  have hnext : Nat.maxPrimeFac (a * p + 1) = q := by rw [heq]; exact hrowb.1
  have hsource : comparisonSign (a * p) = 1 := by
    simp only [comparisonSign, hrowa.1, hnext, if_pos hpq]
  by_cases hb1 : b = 1
  · rw [plusSeed, if_pos hb1]
    have hcenter : a * p = q - 1 := by simp only [hb1, one_mul] at heq; omega
    rw [hcenter]
    exact prime_center_forward_seed hN hq (hp3.trans hpq.le) (by omega)
  · have hb2 : 2 ≤ b := by omega
    by_cases hbp : b < p
    · rw [plusSeed, if_neg hb1, if_pos hbp]
      obtain ⟨ht2, htn, hmax, _hother, hsign, _hclean⟩ :=
        euclidean_plus_target hp hp3 hb2 hba hbp heq
      refine ⟨ht2, htn.le.trans hcut, ?_, Or.inl ⟨p, Or.inl hrowa.1, Or.inl hmax⟩⟩
      rw [hsign, hsource]
    · rw [plusSeed, if_neg hb1, if_neg hbp]
      obtain ⟨ht2, htn, hmax, _hother, hsign, _hclean⟩ :=
        complement_plus_target hp hq hpq (by omega : p ≤ b) heq
      refine ⟨ht2, htn.le.trans hcut, ?_, Or.inl ⟨q, Or.inr hnext, Or.inl hmax⟩⟩
      rw [hsign, hsource]

/-- All negative-source branches are legal actual seeds. No enlarged prefix or
formal source label is admitted by this theorem. -/
theorem minusSeed_isSeed {N a b p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hpq : p < q)
    (hb : 1 ≤ b) (hba : b < a)
    (hsa : Nat.maxPrimeFac a < p) (hsb : Nat.maxPrimeFac b < q)
    (heq : b * q + 1 = a * p) (hcut : b * q ≤ N) :
    IsSeed N (b * q) (minusSeed a b p q) := by
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hrowa := strict_row_cell ha0 hp hsa
  have hrowb := strict_row_cell hb0 hq hsb
  have hnext : Nat.maxPrimeFac (b * q + 1) = p := by rw [heq]; exact hrowa.1
  have hsource : comparisonSign (b * q) = -1 := by
    apply (comparisonSign_eq_neg_one_iff _).mpr
    rw [hnext, hrowb.1]
    exact hpq
  by_cases hb1 : b = 1
  · rw [minusSeed, if_pos hb1]
    have hcenter : b * q = q := by simp only [hb1, one_mul]
    rw [hcenter]
    exact prime_center_backward_seed hq (hp3.trans hpq.le) (by omega)
  · have hb2 : 2 ≤ b := by omega
    by_cases hbp : b < p
    · rw [minusSeed, if_neg hb1, if_pos hbp]
      obtain ⟨ht2, htn, _hother, hmax, hsign, _hclean⟩ :=
        euclidean_minus_target hp hp3 hb2 hba hbp heq
      refine ⟨ht2, htn.le.trans hcut, ?_, Or.inl ⟨p, Or.inr hnext, Or.inr hmax⟩⟩
      rw [hsign, hsource]
      norm_num
    · rw [minusSeed, if_neg hb1, if_neg hbp]
      obtain ⟨ht2, htn, _hother, hmax, hsign, _hclean⟩ :=
        complement_minus_target hp hq hpq (by omega : p ≤ b) heq
      refine ⟨ht2, htn.le.trans hcut, ?_, Or.inl ⟨q, Or.inl hrowb.1, Or.inr hmax⟩⟩
      rw [hsign, hsource]
      norm_num

/- ## Specialization to the actual clean source roots -/

/-- Kernel-verified total correctness of the explicit rule for every clean
source `3 ≤ n ≤ N`, `3 ≤ N`. In particular no hypothetical primality or
smoothness tests are added to the actual-source hypotheses. -/
theorem unitGapSeed_isSeed {N n : ℕ} (hN : 3 ≤ N) (hn : 3 ≤ n) (hnN : n ≤ N)
    (hclean : CleanComparison n) : IsSeed N n (unitGapSeed N n) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hq := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  have hc := cofactor_pos (by omega : 0 < n)
  have hcnext := cofactor_pos (by omega : 0 < n + 1)
  obtain ⟨hsm, hsmnext⟩ :=
    (cleanComparison_iff_strict_smoothness (by omega : 2 ≤ n)).mp hclean
  by_cases hlt : Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)
  · have hba := (maxPrimeFac_lt_iff_cofactor_lt hn).mp hlt
    have heq : cofactor n * Nat.maxPrimeFac n + 1 =
        cofactor (n + 1) * Nat.maxPrimeFac (n + 1) := by
      rw [cofactor_mul_maxPrimeFac, cofactor_mul_maxPrimeFac]
    have hs := plusSeed_isSeed hN hp hq (clean_maxPrimeFac_ge_three hn hclean.1)
      hlt (by omega : 1 ≤ cofactor (n + 1)) hba hsm hsmnext heq
      (by simpa only [cofactor_mul_maxPrimeFac] using hnN)
    simpa only [cofactor_mul_maxPrimeFac, unitGapSeed, if_pos hlt] using hs
  · have hne := no_adjacent_tie n
    have hgt : Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n := by omega
    have hba := (maxPrimeFac_next_lt_iff_cofactor_lt hn).mp hgt
    have heq : cofactor n * Nat.maxPrimeFac n + 1 =
        cofactor (n + 1) * Nat.maxPrimeFac (n + 1) := by
      rw [cofactor_mul_maxPrimeFac, cofactor_mul_maxPrimeFac]
    have hs := minusSeed_isSeed hq hp (clean_maxPrimeFac_ge_three (by omega) hclean.2)
      hgt (by omega : 1 ≤ cofactor n) hba hsmnext hsm heq
      (by simpa only [cofactor_mul_maxPrimeFac] using hnN)
    simpa only [cofactor_mul_maxPrimeFac, unitGapSeed, if_neg hlt] using hs

/-- Exact seed existence: one actual opposite-sign comparison in the *original*
prefix, sharing an actual maximum or actual cofactor. This is not a matching
or injectivity theorem. -/
theorem clean_unitGap_seed_exists {N n : ℕ} (hN : 3 ≤ N) (hn : 3 ≤ n) (hnN : n ≤ N)
    (hclean : CleanComparison n) :
    ∃ t : ℕ, 2 ≤ t ∧ t ≤ N ∧ comparisonSign t = -comparisonSign n ∧
      (SharesActualPrime n t ∨ SharesActualCofactor n t) :=
  ⟨unitGapSeed N n, unitGapSeed_isSeed hN hn hnN hclean⟩

/-- The auxiliary source `2` maps to `3` and retains the actual prime `3`. -/
theorem auxiliary_two_seed {N : ℕ} (hN : 3 ≤ N) : IsSeed N 2 (unitGapSeed N 2) := by
  have hcof2 : cofactor 2 = 1 := (cofactor_eq_one_iff (by omega : 2 ≤ 2)).mpr Nat.prime_two
  have hformula : unitGapSeed N 2 = 3 := by
    simp only [unitGapSeed, Nat.prime_two.maxPrimeFac_eq_self,
      show 2 + 1 = 3 by omega, Nat.prime_three.maxPrimeFac_eq_self,
      show 2 < 3 by omega, if_true, plusSeed, fallback_three.2, hcof2, hN]
  have hs2 : comparisonSign 2 = 1 := by
    simpa only [show 3 - 1 = 2 by omega] using
      (prime_center_signs Nat.prime_three (by omega)).2.2.1
  rw [hformula]
  refine ⟨by omega, hN, ?_, Or.inl ⟨3, Or.inr ?_, Or.inl Nat.prime_three.maxPrimeFac_eq_self⟩⟩
  · rw [fallback_three.1, hs2]
  · exact Nat.prime_three.maxPrimeFac_eq_self

/-- Including the auxiliary source, the explicit map is total on every clean
comparison in `[2,N]`, provided `N ≥ 3`. No assertion is made for `N=2`. -/
theorem clean_prefix_seed_exists {N n : ℕ} (hN : 3 ≤ N) (hn : 2 ≤ n) (hnN : n ≤ N)
    (hclean : CleanComparison n) : ∃ t : ℕ, IsSeed N n t := by
  by_cases hn2 : n = 2
  · subst n
    exact ⟨unitGapSeed N 2, auxiliary_two_seed hN⟩
  · exact ⟨unitGapSeed N n, unitGapSeed_isSeed hN (by omega) hnN hclean⟩

end Erdos371.UnitGap

#print axioms Erdos371.UnitGap.CleanRoot
#print axioms Erdos371.UnitGap.CleanComparison
#print axioms Erdos371.UnitGap.HasActualPrime
#print axioms Erdos371.UnitGap.HasActualCofactor
#print axioms Erdos371.UnitGap.SharesActualPrime
#print axioms Erdos371.UnitGap.SharesActualCofactor
#print axioms Erdos371.UnitGap.IsSeed
#print axioms Erdos371.UnitGap.cleanRoot_iff_cofactor_max_lt
#print axioms Erdos371.UnitGap.cleanComparison_iff_strict_smoothness
#print axioms Erdos371.UnitGap.clean_maxPrimeFac_ge_three
#print axioms Erdos371.UnitGap.actual_row_cell
#print axioms Erdos371.UnitGap.strict_row_cell
#print axioms Erdos371.UnitGap.euclidean_plus_normalize
#print axioms Erdos371.UnitGap.euclidean_minus_normalize
#print axioms Erdos371.UnitGap.complement_plus_normalize
#print axioms Erdos371.UnitGap.complement_minus_normalize
#print axioms Erdos371.UnitGap.complement_plus_seed
#print axioms Erdos371.UnitGap.complement_minus_seed
#print axioms Erdos371.UnitGap.complement_below_source
#print axioms Erdos371.UnitGap.euclidean_plus_target
#print axioms Erdos371.UnitGap.euclidean_minus_target
#print axioms Erdos371.UnitGap.complement_plus_target
#print axioms Erdos371.UnitGap.complement_minus_target
#print axioms Erdos371.UnitGap.prime_center_signs
#print axioms Erdos371.UnitGap.fallback_three
#print axioms Erdos371.UnitGap.prime_center_forward_seed
#print axioms Erdos371.UnitGap.prime_center_backward_seed
#print axioms Erdos371.UnitGap.terminal_prime_center_seed
#print axioms Erdos371.UnitGap.plusSeed
#print axioms Erdos371.UnitGap.minusSeed
#print axioms Erdos371.UnitGap.unitGapSeed
#print axioms Erdos371.UnitGap.plusSeed_isSeed
#print axioms Erdos371.UnitGap.minusSeed_isSeed
#print axioms Erdos371.UnitGap.unitGapSeed_isSeed
#print axioms Erdos371.UnitGap.clean_unitGap_seed_exists
#print axioms Erdos371.UnitGap.auxiliary_two_seed
#print axioms Erdos371.UnitGap.clean_prefix_seed_exists
