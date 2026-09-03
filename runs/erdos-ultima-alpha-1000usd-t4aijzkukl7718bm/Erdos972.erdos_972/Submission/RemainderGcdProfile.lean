import Submission.RemainderPositiveTypeI

/-! A finite gcd-pattern description of the positive Vaughan remainder.
The profile retains its logarithmic argument. A small pattern description is
not, by itself, a uniform growing-modulus correlation bound. -/
namespace Erdos972RemainderGcdProfile

open Finset ArithmeticFunction
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972TypeIPolynomial
open Erdos972DivisorCovariance Erdos972RemainderPositiveTypeI

lemma dvd_gcd_factorial_iff {D d n : ℕ} (hd : d ∈ Ioc 0 D) :
    d ∣ n.gcd D.factorial ↔ d ∣ n := by
  rw [Nat.dvd_gcd_iff]
  exact and_iff_left (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2)

lemma divisorPolynomial_gcd_factorial (D n : ℕ) (a : ℕ → ℝ) :
    divisorPolynomial D a (n.gcd D.factorial) = divisorPolynomial D a n := by
  unfold divisorPolynomial
  apply sum_congr rfl
  intro d hd
  simp only [dvd_gcd_factorial_iff hd]

/-- The logarithm is a separate real argument; the integer argument only
records the finite small-divisor pattern. -/
noncomputable def affineProfile (U V r : ℕ) (x : ℝ) : ℝ :=
  x * divisorPolynomial (U*V) (slopeCoeff U) r +
    divisorPolynomial (U*V) (constantCoeff U V) r

noncomputable def positiveRemainderProfile (U V r : ℕ) (x : ℝ) : ℝ :=
  max (-affineProfile U V r x) 0

lemma typeIPart_gcd_profile {U V n : ℕ} (hV : 0 < V) (hn : V < n) :
    typeIPart U V n = affineProfile U V (n.gcd (U*V).factorial) (Real.log n) := by
  rw [typeIPart_polynomial U V hV (hV.trans hn), cutoff_eq_zero_of_lt _ hn, add_zero]
  simp only [affineProfile, divisorPolynomial_gcd_factorial]

/-- There is no Mangoldt evaluation in this profile of the positive remainder. -/
theorem positive_remainder_gcd_profile {U V n : ℕ} (hU : 1 ≤ U)
    (hV : 0 < V) (hn : V < n) :
    max (typeIIPart U V n) 0 =
      positiveRemainderProfile U V (n.gcd (U*V).factorial) (Real.log n) := by
  rw [positive_remainder_eq_negative_typeI hU, typeIPart_gcd_profile hV hn]
  rfl

/-- Every realized pattern lies in a finite divisor set. -/
lemma gcd_profile_mem (U V n : ℕ) :
    n.gcd (U*V).factorial ∈ (U*V).factorial.divisors := by
  exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, (Nat.factorial_pos _).ne'⟩

lemma affineProfile_sub (U V r : ℕ) (x y : ℝ) :
    affineProfile U V r x - affineProfile U V r y =
      (x-y) * divisorPolynomial (U*V) (slopeCoeff U) r := by
  unfold affineProfile
  ring

lemma affineProfile_lipschitz (U V r : ℕ) (x y : ℝ) :
    |affineProfile U V r x - affineProfile U V r y| ≤ (U*V : ℕ) * |x-y| := by
  rw [affineProfile_sub, abs_mul]
  have hh := (divisorPolynomial_abs_le (U*V) r (slopeCoeff U)).trans (slopeCoeff_mass U (U*V))
  exact (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans_eq (mul_comm _ _)

lemma abs_max_zero_sub_max_zero_le (x y : ℝ) :
    |max x 0 - max y 0| ≤ |x-y| := by
  rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
  · rw [max_eq_right hx, max_eq_right hy, sub_self, abs_zero]
    exact abs_nonneg _
  · rw [max_eq_right hx, max_eq_left hy, zero_sub, abs_neg, abs_of_nonneg hy,
      abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, sub_zero, abs_of_nonneg hx,
      abs_of_nonneg (sub_nonneg.mpr (hy.trans hx))]
    linarith
  · rw [max_eq_left hx, max_eq_left hy]

/-- The nonlinear positive-part operation does not increase the logarithmic
Lipschitz bound within a single gcd pattern. -/
theorem positiveRemainderProfile_lipschitz (U V r : ℕ) (x y : ℝ) :
    |positiveRemainderProfile U V r x - positiveRemainderProfile U V r y| ≤
      (U*V : ℕ) * |x-y| := by
  have hh := abs_max_zero_sub_max_zero_le (-affineProfile U V r x) (-affineProfile U V r y)
  rw [neg_sub_neg, abs_sub_comm (affineProfile U V r y) (affineProfile U V r x)] at hh
  exact hh.trans (affineProfile_lipschitz U V r x y)

/-- Two integers with the same small-divisor pattern can differ only through
the logarithmic argument in the positive remainder. -/
theorem positive_remainder_same_pattern {U V m n : ℕ} (hU : 1 ≤ U) (hV : 0 < V)
    (hm : V < m) (hn : V < n)
    (he : m.gcd (U*V).factorial = n.gcd (U*V).factorial) :
    |max (typeIIPart U V m) 0 - max (typeIIPart U V n) 0| ≤
      (U*V : ℕ) * |Real.log m - Real.log n| := by
  rw [positive_remainder_gcd_profile hU hV hm, positive_remainder_gcd_profile hU hV hn, he]
  exact positiveRemainderProfile_lipschitz _ _ _ _ _

#print axioms positive_remainder_gcd_profile
#print axioms positiveRemainderProfile_lipschitz
#print axioms positive_remainder_same_pattern

end Erdos972RemainderGcdProfile
