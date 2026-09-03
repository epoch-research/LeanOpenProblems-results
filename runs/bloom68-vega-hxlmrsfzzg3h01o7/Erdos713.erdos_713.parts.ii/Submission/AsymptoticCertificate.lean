import Submission.PolynomialCertificate

/-!
# Rational exponents from asymptotically vanishing polynomial residuals

A sequence asymptotic to `c * n ^ a`, with `c > 0`, has rational exponent if a
fixed nonzero polynomial evaluated at `(n, f n)` is little-o of the sum of the
absolute values of its monomials. Both versions of that sum, with `f n` or
`|f n|`, are covered below.

For an irrational exponent the monomial weights are distinct. Normalization
by the largest weight makes the polynomial tend to a nonzero constant and the
sum of absolute monomials tend to a finite constant, contradicting little-o.

This is only a conditional algebraic endgame. In particular, no certificate
for graph extremal numbers is asserted or constructed here.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos713Polynomial

/-- Only the unique largest-weight monomial survives normalization. The
coefficients in this lemma may vanish, and the exponent need not be irrational. -/
lemma tendsto_polynomial_div_rpow_of_unique_max
    {f : ℕ → ℝ} {a c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (s : Finset (ℕ × ℕ)) (d : ℕ × ℕ → ℝ) {p₀ : ℕ × ℕ}
    (hp₀ : p₀ ∈ s)
    (hmax : ∀ p ∈ s, p ≠ p₀ →
      (p.1 : ℝ) + a * (p.2 : ℝ) < (p₀.1 : ℝ) + a * (p₀.2 : ℝ)) :
    Tendsto (fun n : ℕ =>
      (∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2) /
        (n : ℝ) ^ ((p₀.1 : ℝ) + a * (p₀.2 : ℝ)))
      atTop (𝓝 (d p₀ * c ^ p₀.2)) := by
  classical
  let w : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) + a * (p.2 : ℝ)
  have hratio := tendsto_div_rpow_of_equivalent hf
  have hterm : ∀ p ∈ s,
      Tendsto (fun n : ℕ =>
        d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 / (n : ℝ) ^ w p₀)
        atTop (𝓝 (if p = p₀ then d p * c ^ p.2 else 0)) := by
    intro p hp
    have hbase := (hratio.pow p.2).const_mul (d p)
    have hnormalized : Tendsto (fun n : ℕ =>
        d p * (f n / (n : ℝ) ^ a) ^ p.2 * (n : ℝ) ^ (w p - w p₀))
        atTop (𝓝 (if p = p₀ then d p * c ^ p.2 else 0)) := by
      by_cases hpp : p = p₀
      · subst p
        simpa using hbase
      · have hdecay : Tendsto (fun n : ℕ => (n : ℝ) ^ (w p - w p₀))
            atTop (𝓝 (0 : ℝ)) := by
          simpa only [neg_sub] using
            (tendsto_rpow_neg_atTop (sub_pos.mpr (hmax p hp hpp))).comp
              (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa only [if_neg hpp, mul_zero] using hbase.mul hdecay
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (normalized_monomial hn' (f n) (d p) a (w p₀) p).symm
  simpa [← Finset.sum_div, hp₀, w] using tendsto_finset_sum s hterm

/-- A fixed nonzero polynomial whose residual is negligible relative to its
absolute-coefficient monomial sum forces the power-law exponent to be rational.
No positivity assumption on `f` is needed: it follows eventually from `hc` and `hf`. -/
theorem rational_exponent_of_polynomial_isLittleO
    {f : ℕ → ℝ} {a c : ℝ}
    (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (s : Finset (ℕ × ℕ)) (hs : s.Nonempty)
    (d : ℕ × ℕ → ℝ) (hd : ∀ p ∈ s, d p ≠ 0)
    (hP : (fun n : ℕ => ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2)
      =o[atTop] (fun n : ℕ => ∑ p ∈ s, |d p| * (n : ℝ) ^ p.1 * (f n) ^ p.2)) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra ha
  let w : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) + a * (p.2 : ℝ)
  have hw : Function.Injective w := monomial_weight_injective ha
  obtain ⟨p₀, hp₀, hmax⟩ := s.exists_max_image w hs
  have hstrict : ∀ p ∈ s, p ≠ p₀ → w p < w p₀ := by
    intro p hp hne
    exact lt_of_le_of_ne (hmax p hp) (hw.ne hne)
  have hnum := tendsto_polynomial_div_rpow_of_unique_max hf s d hp₀ hstrict
  have hden := tendsto_polynomial_div_rpow_of_unique_max hf s (fun p => |d p|) hp₀
    hstrict
  have hnormalized :
      (fun n : ℕ => (∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2) /
        (n : ℝ) ^ w p₀)
      =o[atTop] (fun n : ℕ => (∑ p ∈ s, |d p| * (n : ℝ) ^ p.1 * (f n) ^ p.2) /
        (n : ℝ) ^ w p₀) := by
    simpa only [div_eq_mul_inv] using
      hP.mul_isBigO (isBigO_refl (fun n : ℕ => ((n : ℝ) ^ w p₀)⁻¹) atTop)
  have hzero := hnormalized.tendsto_zero_of_tendsto hden
  exact (mul_ne_zero (hd p₀ hp₀) (pow_ne_zero _ hc.ne'))
    (tendsto_nhds_unique hnum hzero)

/-- A positive leading coefficient implies eventual positivity, for any real exponent. -/
lemma eventually_pos_of_equivalent_rpow {f : ℕ → ℝ} {a c : ℝ}
    (hc : 0 < c) (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a)) :
    ∀ᶠ n : ℕ in atTop, 0 < f n := by
  have hratio := (tendsto_div_rpow_of_equivalent hf).eventually (eventually_gt_nhds hc)
  filter_upwards [hratio, eventually_gt_atTop 0] with n hn hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  exact (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hnpos' a)).mp hn

/-- The version with an everywhere nonnegative denominator, using `|f n|`. -/
theorem rational_exponent_of_polynomial_isLittleO_abs
    {f : ℕ → ℝ} {a c : ℝ}
    (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (s : Finset (ℕ × ℕ)) (hs : s.Nonempty)
    (d : ℕ × ℕ → ℝ) (hd : ∀ p ∈ s, d p ≠ 0)
    (hP : (fun n : ℕ => ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2)
      =o[atTop] (fun n : ℕ => ∑ p ∈ s, |d p| * (n : ℝ) ^ p.1 * |f n| ^ p.2)) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply rational_exponent_of_polynomial_isLittleO hc hf s hs d hd
  refine hP.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [eventually_pos_of_equivalent_rpow hc hf] with n hn
  simp only [abs_of_pos hn]

/- Concrete nonvacuous certificates for `Y² - X³`. -/

namespace Examples

/-- The two distinct monomials of `Y² - X³`. -/
def squareCubeSupport : Finset (ℕ × ℕ) := {(0, 2), (3, 0)}

/-- Coefficients are only used on `squareCubeSupport`. -/
def squareCubeCoeff (p : ℕ × ℕ) : ℝ := if p = (0, 2) then 1 else -1

lemma squareCubeSupport_nonempty : squareCubeSupport.Nonempty := by
  simp [squareCubeSupport]

lemma squareCubeCoeff_ne_zero (p : ℕ × ℕ) : squareCubeCoeff p ≠ 0 := by
  unfold squareCubeCoeff
  split <;> norm_num

lemma squareCube_eval (f : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ squareCubeSupport, squareCubeCoeff p * (n : ℝ) ^ p.1 * (f n) ^ p.2) =
      (f n) ^ 2 - (n : ℝ) ^ 3 := by
  simp [squareCubeSupport, squareCubeCoeff, sub_eq_add_neg]

lemma squareCube_abs_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ squareCubeSupport, |squareCubeCoeff p| * (n : ℝ) ^ p.1 * |f n| ^ p.2) =
      (f n) ^ 2 + (n : ℝ) ^ 3 := by
  simp [squareCubeSupport, squareCubeCoeff, sq_abs]

/-- A real-valued power; there is no rounding to natural numbers. -/
noncomputable def powerThreeHalves (n : ℕ) : ℝ := (n : ℝ) ^ (3 / 2 : ℝ)

lemma powerThreeHalves_nonneg (n : ℕ) : 0 ≤ powerThreeHalves n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

lemma powerThreeHalves_sq (n : ℕ) : (powerThreeHalves n) ^ 2 = (n : ℝ) ^ 3 := by
  unfold powerThreeHalves
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

/-- In fact every real-valued sequence asymptotic to `n^(3/2)` has this
approximate polynomial certificate. -/
lemma squareCube_isLittleO_of_equivalent {f : ℕ → ℝ}
    (hf : f ~[atTop] powerThreeHalves) :
    (fun n : ℕ =>
      ∑ p ∈ squareCubeSupport, squareCubeCoeff p * (n : ℝ) ^ p.1 * (f n) ^ p.2)
      =o[atTop] (fun n : ℕ =>
        ∑ p ∈ squareCubeSupport, |squareCubeCoeff p| * (n : ℝ) ^ p.1 * |f n| ^ p.2) := by
  have hsq : (fun n : ℕ => (f n) ^ 2) ~[atTop] (fun n : ℕ => (n : ℝ) ^ 3) :=
    (hf.pow 2).congr_right (Eventually.of_forall powerThreeHalves_sq)
  have hbound : (fun n : ℕ => (n : ℝ) ^ 3)
      =O[atTop] (fun n : ℕ => (f n) ^ 2 + (n : ℝ) ^ 3) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    have hcube : 0 ≤ (n : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hcube,
      Real.norm_of_nonneg (add_nonneg (sq_nonneg (f n)) hcube), one_mul]
    exact le_add_of_nonneg_left (sq_nonneg (f n))
  simpa only [squareCube_eval, squareCube_abs_sum] using hsq.isLittleO.trans_isBigO hbound

/-- The unshifted example satisfies the polynomial relation at every `n`, including zero. -/
theorem powerThreeHalves_polynomial_eq_zero (n : ℕ) :
    (∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (powerThreeHalves n) ^ p.2) = 0 := by
  rw [squareCube_eval, powerThreeHalves_sq, sub_self]

theorem powerThreeHalves_certificate :
    (fun n : ℕ => ∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (powerThreeHalves n) ^ p.2)
      =o[atTop] (fun n : ℕ => ∑ p ∈ squareCubeSupport,
        |squareCubeCoeff p| * (n : ℝ) ^ p.1 * |powerThreeHalves n| ^ p.2) :=
  squareCube_isLittleO_of_equivalent IsEquivalent.refl

/-- All hypotheses of the generic rationality theorem are discharged, rather
than postulated, in this concrete application. -/
theorem powerThreeHalves_rational_via_certificate :
    (3 / 2 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply rational_exponent_of_polynomial_isLittleO_abs (c := 1) (by norm_num)
    (f := powerThreeHalves) _ squareCubeSupport squareCubeSupport_nonempty squareCubeCoeff
    (fun p _ => squareCubeCoeff_ne_zero p) powerThreeHalves_certificate
  simpa only [one_mul] using (IsEquivalent.refl : powerThreeHalves ~[atTop] powerThreeHalves)

/-- A perturbation for which `Y² - X³` is not identically zero. -/
noncomputable def shiftedPowerThreeHalves (n : ℕ) : ℝ := powerThreeHalves n + 1

lemma shiftedPowerThreeHalves_equivalent :
    shiftedPowerThreeHalves ~[atTop] powerThreeHalves := by
  change (fun n : ℕ => powerThreeHalves n + 1) ~[atTop] powerThreeHalves
  apply IsEquivalent.refl.add_const_of_norm_tendsto_atTop
  have heq : (norm ∘ powerThreeHalves) = powerThreeHalves := by
    funext n
    exact Real.norm_of_nonneg (powerThreeHalves_nonneg n)
  rw [heq]
  exact (tendsto_rpow_atTop (by norm_num : 0 < (3 / 2 : ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

lemma shiftedPowerThreeHalves_polynomial_eq (n : ℕ) :
    (∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (shiftedPowerThreeHalves n) ^ p.2) =
      2 * powerThreeHalves n + 1 := by
  rw [squareCube_eval]
  unfold shiftedPowerThreeHalves
  nlinarith [powerThreeHalves_sq n]

/-- The residual of the shifted example is everywhere positive, not just nonzero somewhere. -/
theorem shiftedPowerThreeHalves_polynomial_pos (n : ℕ) :
    0 < ∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (shiftedPowerThreeHalves n) ^ p.2 := by
  rw [shiftedPowerThreeHalves_polynomial_eq]
  linarith [powerThreeHalves_nonneg n]

theorem shiftedPowerThreeHalves_certificate :
    (fun n : ℕ => ∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (shiftedPowerThreeHalves n) ^ p.2)
      =o[atTop] (fun n : ℕ => ∑ p ∈ squareCubeSupport,
        |squareCubeCoeff p| * (n : ℝ) ^ p.1 * |shiftedPowerThreeHalves n| ^ p.2) :=
  squareCube_isLittleO_of_equivalent shiftedPowerThreeHalves_equivalent

/-- The usual relative error tends to zero despite the strictly positive residual. -/
theorem shiftedPowerThreeHalves_relative_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) ^ (3 / 2 : ℝ) + 1) ^ 2 - (n : ℝ) ^ 3) /
        (((n : ℝ) ^ (3 / 2 : ℝ) + 1) ^ 2 + (n : ℝ) ^ 3))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [squareCube_eval shiftedPowerThreeHalves, squareCube_abs_sum shiftedPowerThreeHalves]
    using shiftedPowerThreeHalves_certificate.tendsto_div_nhds_zero

/-- A second genuine application: its certificate is only asymptotic, not exact. -/
theorem shiftedPowerThreeHalves_rational_via_certificate :
    (3 / 2 : ℝ) ∈ Set.range ((↑) : ℚ → ℝ) := by
  apply rational_exponent_of_polynomial_isLittleO_abs (c := 1) (by norm_num)
    (f := shiftedPowerThreeHalves) _ squareCubeSupport squareCubeSupport_nonempty squareCubeCoeff
    (fun p _ => squareCubeCoeff_ne_zero p) shiftedPowerThreeHalves_certificate
  simpa only [one_mul] using shiftedPowerThreeHalves_equivalent

/-- An integer-valued example, like an extremal-number sequence. -/
noncomputable def roundedPowerThreeHalves (n : ℕ) : ℕ := ⌊powerThreeHalves n⌋₊

lemma roundedPowerThreeHalves_equivalent :
    (fun n : ℕ => (roundedPowerThreeHalves n : ℝ)) ~[atTop] powerThreeHalves := by
  have ht : Tendsto powerThreeHalves atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (3 / 2 : ℝ))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact (isEquivalent_nat_floor (R := ℝ)).comp_tendsto ht

/-- The approximate certificate also holds for a natural-number sequence;
no exact polynomial equality is imposed on its rounded values. -/
theorem roundedPowerThreeHalves_certificate :
    (fun n : ℕ => ∑ p ∈ squareCubeSupport,
      squareCubeCoeff p * (n : ℝ) ^ p.1 * (roundedPowerThreeHalves n : ℝ) ^ p.2)
      =o[atTop] (fun n : ℕ => ∑ p ∈ squareCubeSupport,
        |squareCubeCoeff p| * (n : ℝ) ^ p.1 * |(roundedPowerThreeHalves n : ℝ)| ^ p.2) :=
  squareCube_isLittleO_of_equivalent roundedPowerThreeHalves_equivalent

theorem roundedPowerThreeHalves_relative_error_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (((roundedPowerThreeHalves n : ℝ)) ^ 2 - (n : ℝ) ^ 3) /
        (((roundedPowerThreeHalves n : ℝ)) ^ 2 + (n : ℝ) ^ 3))
      atTop (𝓝 (0 : ℝ)) := by
  simpa only [squareCube_eval (fun n => (roundedPowerThreeHalves n : ℝ)),
    squareCube_abs_sum (fun n => (roundedPowerThreeHalves n : ℝ))] using
    roundedPowerThreeHalves_certificate.tendsto_div_nhds_zero

end Examples

end Erdos713Polynomial

#print axioms Erdos713Polynomial.rational_exponent_of_polynomial_isLittleO
#print axioms Erdos713Polynomial.rational_exponent_of_polynomial_isLittleO_abs
#print axioms Erdos713Polynomial.Examples.powerThreeHalves_polynomial_eq_zero
#print axioms Erdos713Polynomial.Examples.powerThreeHalves_rational_via_certificate
#print axioms Erdos713Polynomial.Examples.shiftedPowerThreeHalves_polynomial_pos
#print axioms Erdos713Polynomial.Examples.shiftedPowerThreeHalves_relative_error_tendsto_zero
#print axioms Erdos713Polynomial.Examples.shiftedPowerThreeHalves_rational_via_certificate
