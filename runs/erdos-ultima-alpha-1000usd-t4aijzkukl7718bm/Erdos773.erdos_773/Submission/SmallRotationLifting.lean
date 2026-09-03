import FormalConjecturesUtil

/-!
A bounded-coefficient lifting lemma for integer digit vectors. This is an
auxiliary result, not a proof of the square-Sidon conjecture. The base bound
is essential: unrestricted specialization does not preserve vector rotations.
-/
namespace Erdos773.SmallRotationLifting
open Finset
set_option maxHeartbeats 1000000

def value {n : ℕ} (B : ℤ) (a : Fin n → ℤ) : ℤ :=
  ∑ i, a i * B ^ i.val

/-- Signed digits of absolute value below the positive radix cannot evaluate
to zero unless they all vanish. -/
theorem signed_zero {n : ℕ} {B : ℤ} (hB : 0 < B) (a : Fin n → ℤ)
    (ha : ∀ i, |a i| < B) (he : value B a = 0) : ∀ i, a i = 0 := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have hex : value B a = a 0 + B * value B (fun i : Fin n => a i.succ) := by
      simp only [value, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ, pow_succ, mul_sum]
      congr 1
      apply sum_congr rfl
      intro i hi
      ring
    have hd : B ∣ a 0 := ⟨-value B (fun i : Fin n => a i.succ), by
      rw [hex] at he
      linarith⟩
    have hz : a 0 = 0 := Int.eq_zero_of_abs_lt_dvd hd (ha 0)
    have ht : value B (fun i : Fin n => a i.succ) = 0 := by
      rw [hex, hz, zero_add] at he
      exact (mul_eq_zero.mp he).resolve_left hB.ne'
    have hi := ih (fun i : Fin n => a i.succ) (fun i => ha i.succ) ht
    intro i
    exact Fin.cases hz hi i

lemma linear_value {n : ℕ} (B p r q : ℤ) (a b c : Fin n → ℤ) :
    value B (fun i => p*a i+r*b i-q*c i) =
      p*value B a+r*value B b-q*value B c := by
  simp only [value, sub_mul, add_mul, mul_assoc, sum_sub_distrib,
    sum_add_distrib, mul_sum]

/-- A scalar relation with sufficiently small digit discrepancies lifts
coordinatewise; no conclusion is asserted when that hypothesis fails. -/
theorem linear_lift {n : ℕ} {B p r q : ℤ} (hB : 0 < B)
    (a b c : Fin n → ℤ)
    (hsmall : ∀ i, |p*a i+r*b i-q*c i| < B)
    (he : p*value B a+r*value B b=q*value B c) :
    ∀ i, p*a i+r*b i=q*c i := by
  have hz : value B (fun i => p*a i+r*b i-q*c i) = 0 := by
    rw [linear_value, he, sub_self]
  intro i
  exact sub_eq_zero.mp (signed_zero hB _ hsmall hz i)

lemma discrepancy_bound {p r q H : ℤ} {x y z : ℤ}
    (hx : |x| ≤ H) (hy : |y| ≤ H) (hz : |z| ≤ H) :
    |p*x+r*y-q*z| ≤ (|p|+|r|+|q|)*H := by
  calc
    _ ≤ |p*x+r*y|+|q*z| := abs_sub _ _
    _ ≤ (|p*x|+|r*y|)+|q*z| := add_le_add (abs_add_le (p*x) (r*y)) (le_refl |q*z|)
    _ = |p| *|x|+|r| *|y|+|q| *|z| := by simp only [abs_mul]
    _ ≤ |p| *H+|r| *H+|q| *H :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg p))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg r)))
        (mul_le_mul_of_nonneg_left hz (abs_nonneg q))
    _ = _ := by ring

/-- An orthogonal mixing of two equal-length vectors cannot have that same
length unless their inner product vanishes (when both coefficients are
nonzero). Only the first row of the rotation is needed. -/
theorem orthogonal_of_equal_norm {ι : Type*} [Fintype ι]
    (a b c : ι → ℤ) {p r q : ℤ} (hp : p ≠ 0) (hr : r ≠ 0)
    (hpyth : q^2 = p^2+r^2)
    (hab : (∑ i, a i^2) = ∑ i, b i^2)
    (hac : (∑ i, a i^2) = ∑ i, c i^2)
    (hrel : ∀ i, p*a i+r*b i=q*c i) :
    (∑ i, a i*b i) = 0 := by
  have hsum : p^2*(∑ i, a i^2)+r^2*(∑ i, b i^2)+
      2*p*r*(∑ i, a i*b i) = q^2*(∑ i, c i^2) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hh := congrArg (fun x : ℤ => x^2) (hrel i)
    nlinarith only [hh]
  rw [← hab, ← hac, hpyth] at hsum
  have hz : (2*p*r)*(∑ i, a i*b i) = 0 := by nlinarith only [hsum]
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hp) hr)

/-- A positive common-norm digit class excludes rotations whose coefficients
fit the explicit no-carry bound. This is not a bound for arbitrary rotations. -/
theorem no_small_rotation {n : ℕ} {B H p r q : ℤ}
    (hB : 0 < B) (hp : p ≠ 0) (hr : r ≠ 0)
    (hpyth : q^2 = p^2+r^2) (hsize : (|p|+|r|+|q|)*H < B)
    (a b c : Fin n → ℤ)
    (ha : ∀ i, |a i| ≤ H) (hb : ∀ i, |b i| ≤ H) (hc : ∀ i, |c i| ≤ H)
    (hab : (∑ i, a i^2) = ∑ i, b i^2)
    (hac : (∑ i, a i^2) = ∑ i, c i^2)
    (hpos : 0 < ∑ i, a i*b i) :
    p*value B a+r*value B b ≠ q*value B c := by
  intro he
  have hrel := linear_lift hB a b c
    (fun i => (discrepancy_bound (ha i) (hb i) (hc i)).trans_lt hsize) he
  have hz := orthogonal_of_equal_norm a b c hp hr hpyth hab hac hrel
  omega

/-- A denominator-only version of the bound: a rational unit-circle point
has both numerator coordinates at most its positive denominator. -/
theorem no_bounded_denominator {n : ℕ} {B H Q p r q : ℤ}
    (hB : 0 < B) (hH : 0 ≤ H) (hq : 0 < q) (hqQ : q ≤ Q)
    (hp : p ≠ 0) (hr : r ≠ 0) (hpyth : q^2 = p^2+r^2)
    (hsize : 3*Q*H < B) (a b c : Fin n → ℤ)
    (ha : ∀ i, |a i| ≤ H) (hb : ∀ i, |b i| ≤ H) (hc : ∀ i, |c i| ≤ H)
    (hab : (∑ i, a i^2) = ∑ i, b i^2)
    (hac : (∑ i, a i^2) = ∑ i, c i^2)
    (hpos : 0 < ∑ i, a i*b i) :
    p*value B a+r*value B b ≠ q*value B c := by
  have hpq : |p| ≤ q := by
    have hs := sq_abs p
    have hn := abs_nonneg p
    nlinarith only [hs, hn, hq, hpyth, sq_nonneg r]
  have hrq : |r| ≤ q := by
    have hs := sq_abs r
    have hn := abs_nonneg r
    nlinarith only [hs, hn, hq, hpyth, sq_nonneg p]
  have hcq : |p|+|r|+|q| ≤ 3*Q := by
    rw [abs_of_pos hq]
    omega
  exact no_small_rotation hB hp hr hpyth
    ((mul_le_mul_of_nonneg_right hcq hH).trans_lt hsize) a b c ha hb hc hab hac hpos

#print axioms signed_zero
#print axioms linear_lift
#print axioms orthogonal_of_equal_norm
#print axioms no_small_rotation
#print axioms no_bounded_denominator
end Erdos773.SmallRotationLifting
