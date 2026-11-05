import Submission.SmallDivisorAverage

/-!
# Polynomial values and the original floored divisor sum

The absolute values of an integer polynomial give a residue-invariant natural
sequence. For an irreducible polynomial of natural degree at least two this
sequence is positive everywhere, since an integer root would give a factor
`X - C a`. Eventual positivity on the integers also implies that the original
floored sum and the absolute-value sum differ eventually by a constant.

This module only sets up the polynomial sequence and transfers normalized limits
between the two sums and between real and natural cutoffs. It does not establish
root-count limits or the divisor-average conjecture.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

/-- The natural absolute value of a polynomial evaluated at a natural input. -/
def polynomialAbsValue (f : ℤ[X]) (n : ℕ) : ℕ :=
  (f.eval (n : ℤ)).natAbs

/-- The original floored polynomial divisor sum, including the input zero.
Each natural divisor count is cast to `ℝ` before summing, as in the original
specification. The transparent alias `sigma0` denotes `sigma 0`. -/
noncomputable def flooredPolynomialSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Iic (Nat.floor x),
    (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)

/-- Expand the original floored sum as a real sum of divisor counts. -/
theorem flooredPolynomialSum_eq_sum (f : ℤ[X]) (x : ℝ) :
    flooredPolynomialSum f x =
      ∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ) := rfl

/-- The divisor sum along absolute polynomial values at a real cutoff. -/
noncomputable def absPolynomialSum (f : ℤ[X]) (x : ℝ) : ℝ :=
  divisorAlong (polynomialAbsValue f) (Nat.floor x)

/-- Integer congruence is preserved by evaluation of an integer polynomial. -/
theorem polynomial_eval_modEq (f : ℤ[X]) {q a b : ℤ}
    (h : a ≡ b [ZMOD q]) : f.eval a ≡ f.eval b [ZMOD q] := by
  exact Int.modEq_iff_dvd.mpr (h.dvd.trans (sub_dvd_eval_sub b a f))

/-- The divisibility predicate for absolute polynomial values depends only on
residues, in the form required by the small-divisor averaging lemmas. -/
theorem polynomialAbsValue_mod_dvd (f : ℤ[X]) :
    ∀ q : ℕ, 0 < q → ∀ n : ℕ,
      q ∣ polynomialAbsValue f n ↔ q ∣ polynomialAbsValue f (n % q) := by
  intro q _hq n
  unfold polynomialAbsValue
  rw [← Int.natCast_dvd, ← Int.natCast_dvd]
  exact (polynomial_eval_modEq f
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq n q).symm)).dvd_iff

/-- An irreducible integer polynomial of degree at least two has no integer
root: a root would supply the nonunit factor `X - C a`. -/
theorem polynomial_eval_ne_zero (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) (a : ℤ) : f.eval a ≠ 0 := by
  intro ha
  obtain ⟨g, hg⟩ := dvd_iff_isRoot.mpr (show f.IsRoot a from ha)
  rcases hf.isUnit_or_isUnit hg with hu | hu
  · have hunit := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at hunit
    omega
  · have hdegree : f.natDegree = 1 := by
      rw [hg, natDegree_mul (X_sub_C_ne_zero a) hu.ne_zero,
        natDegree_X_sub_C, natDegree_eq_zero_of_isUnit hu, add_zero]
    omega

/-- Absolute polynomial values are positive at every natural input under the
irreducibility and degree hypotheses; no sign assumption on `f` is needed. -/
theorem polynomialAbsValue_pos (f : ℤ[X]) (hf : Irreducible f)
    (hdeg : 2 ≤ f.natDegree) : ∀ n : ℕ, 0 < polynomialAbsValue f n := by
  intro n
  exact Int.natAbs_pos.mpr (polynomial_eval_ne_zero f hf hdeg (n : ℤ))

/-- The natural floor of a nonnegative integer is its natural absolute value. -/
theorem floor_nonneg_abs (z : ℤ) (h : 0 ≤ z) : Nat.floor z = z.natAbs := by
  cases z with
  | ofNat n => simp
  | negSucc n => omega

/-- The original eventual positivity hypothesis on integer inputs also holds
on natural inputs. -/
theorem eventual_natural_positivity (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ) :=
  (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop).eventually h

/-- In particular, the absolute-value sequence is eventually positive under
the original eventual positivity hypothesis alone. -/
theorem eventual_polynomialAbsValue_pos (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, 0 < polynomialAbsValue f n := by
  filter_upwards [eventual_natural_positivity f h] with n hn
  apply Int.natAbs_pos.mpr
  omega

/-- Eventually, the floor convention in the original sum agrees with taking
the absolute value of the polynomial. -/
theorem eventual_floor_abs (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∀ᶠ n : ℕ in atTop, Nat.floor (f.eval (n : ℤ)) = polynomialAbsValue f n := by
  filter_upwards [eventual_natural_positivity f h] with n hn
  exact floor_nonneg_abs _ (le_trans (by norm_num) hn)

/-- Two sequences that agree eventually have real-cutoff partial sums whose
difference is eventually constant. The inclusive interval contains zero. -/
theorem finite_tail_difference (a b : ℕ → ℝ)
    (h : a =ᶠ[atTop] b) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      (∑ n ∈ Finset.Iic (Nat.floor x), a n) -
        (∑ n ∈ Finset.Iic (Nat.floor x), b n) = C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨∑ n ∈ Finset.Iic N, (a n - b n), ?_⟩
  filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
  have hNx : N ≤ Nat.floor x := Nat.le_floor hx
  rw [← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset
    (show Finset.Iic N ⊆ Finset.Iic (Nat.floor x) from fun n hn ↦
      Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hn).trans hNx))
  intro n _ hn
  have hNn : N ≤ n := by
    have : ¬n ≤ N := by simpa only [Finset.mem_Iic] using hn
    omega
  rw [hN n hNn, sub_self]

/-- The original floor convention and the absolute-value convention differ
only by a fixed initial contribution under eventual positivity. -/
theorem floor_abs_constant_difference (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ C : ℝ, ∀ᶠ x : ℝ in atTop,
      flooredPolynomialSum f x - absPolynomialSum f x = C := by
  simp only [flooredPolynomialSum_eq_sum, absPolynomialSum, divisorAlong]
  apply finite_tail_difference
  filter_upwards [eventual_floor_abs f h] with n hn
  simp only [hn, ArithmeticFunction.sigma0]

/-- The fixed initial difference vanishes after normalization by `x * log x`. -/
theorem floor_abs_difference_vanishes (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    Tendsto (fun x : ℝ ↦
      (flooredPolynomialSum f x - absPolynomialSum f x) / (x * Real.log x))
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := floor_abs_constant_difference f h
  have ht : Tendsto (fun x : ℝ ↦ C / (x * Real.log x)) atTop (𝓝 0) :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).const_div_atTop C
  apply ht.congr'
  filter_upwards [hC] with x hx
  rw [hx]

/-- At real cutoffs, the floor and absolute-value conventions give equivalent
normalized limits under the original eventual positivity hypothesis. -/
theorem floor_abs_limit_iff (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) (c : ℝ) :
    Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x))
        atTop (𝓝 c) ↔
      Tendsto (fun x : ℝ ↦ absPolynomialSum f x / (x * Real.log x))
        atTop (𝓝 c) := by
  have he := floor_abs_difference_vanishes f h
  constructor
  · intro ht
    have hid : (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x) -
        (flooredPolynomialSum f x - absPolynomialSum f x) / (x * Real.log x)) =
        (fun x : ℝ ↦ absPolynomialSum f x / (x * Real.log x)) := by
      funext x
      simp only [div_eq_mul_inv]
      ring
    simpa only [hid, sub_zero] using ht.sub he
  · intro ht
    have hid : (fun x : ℝ ↦ absPolynomialSum f x / (x * Real.log x) +
        (flooredPolynomialSum f x - absPolynomialSum f x) / (x * Real.log x)) =
        (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) := by
      funext x
      simp only [div_eq_mul_inv]
      ring
    simpa only [hid, add_zero] using ht.add he

/-- The normalized original floor-sum limit is equivalent to the normalized
natural-cutoff divisor sum along absolute polynomial values. This uses the
real-cutoff transfer from `Submission.RealCutoff` and does not assert that
either limit exists. -/
theorem flooredPolynomialSum_limit_iff (f : ℤ[X])
    (h : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) (c : ℝ) :
    Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x))
        atTop (𝓝 c) ↔
      Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 c) := by
  exact (floor_abs_limit_iff f h c).trans
    (tendsto_floor_normalization_iff
      (A := divisorAlong (polynomialAbsValue f)) (c := c)).symm

end Erdos975Support
