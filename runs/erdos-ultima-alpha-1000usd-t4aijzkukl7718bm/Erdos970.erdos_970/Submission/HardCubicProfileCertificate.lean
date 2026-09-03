import Submission.PrimeAllLogMoments

/-! Exact algebraic certificate for a proposed hard-cutoff cubic profile.
The norm and split-shift integrals are verified exactly. Their transfer to
arithmetic-prime energy is NOT asserted here. These results alone give no
new Jacobsthal exponent. -/
namespace Erdos970.FiniteSelberg
open Finset Real MeasureTheory

noncomputable def hardCubic (u : ℝ) : ℝ :=
  2392 + 11017 * u - 8076 * u ^ 2 + 4667 * u ^ 3

noncomputable def hardCubicCoefficient : Fin 4 → ℝ := ![2392, 11017, -8076, 4667]

noncomputable def hardMonomialNorm (i j : Fin 4) : ℝ :=
  1 / ((i.val : ℝ) + j.val + 1)

noncomputable def hardMonomialEnergy (i j : Fin 4) : ℝ :=
  ((harmonic i.val : ℝ) + (harmonic j.val : ℝ) -
    (harmonic (i.val + j.val) : ℝ)) / ((i.val : ℝ) + j.val + 1) +
    1 / ((i.val : ℝ) + j.val + 1) ^ 2

noncomputable def hardCubicNorm : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    hardCubicCoefficient i * hardMonomialNorm i j * hardCubicCoefficient j

noncomputable def hardCubicEnergy : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    hardCubicCoefficient i * hardMonomialEnergy i j * hardCubicCoefficient j

lemma hardCubicNorm_eq : hardCubicNorm = 4715325794 / 105 := by
  norm_num [hardCubicNorm, hardCubicCoefficient, hardMonomialNorm, Fin.sum_univ_succ]

lemma hardCubicEnergy_eq : hardCubicEnergy = 1410547801651 / 44100 := by
  norm_num [hardCubicEnergy, hardCubicCoefficient, hardMonomialEnergy,
    Fin.sum_univ_succ, harmonic, sum_range_succ]

/-- The proposed energy matrix leaves a strictly positive rational margin at
  the reciprocal-tail budget 2877/10000. -/
lemma hardCubic_margin :
    (1 - 2877 / 10000 : ℝ) * hardCubicNorm - hardCubicEnergy =
      29338709201 / 11025000 := by
  rw [hardCubicNorm_eq, hardCubicEnergy_eq]
  norm_num

lemma hardCubic_margin_pos :
    0 < (1 - 2877 / 10000 : ℝ) * hardCubicNorm - hardCubicEnergy := by
  rw [hardCubic_margin]
  norm_num

lemma hardCubic_derivative_positive (u : ℝ) :
    0 < 11017 - 16152 * u + 14001 * u ^ 2 := by
  nlinarith [sq_nonneg (u - 1)]

lemma hardCubic_positive (u : ℝ) (hu : 0 ≤ u) : 0 < hardCubic u := by
  have hq : 0 < 11017 - 8076 * u + 4667 * u ^ 2 := by
    nlinarith [sq_nonneg (u - 1)]
  have he : hardCubic u = 2392 + u * (11017 - 8076 * u + 4667 * u ^ 2) := by
    unfold hardCubic
    ring
  rw [he]
  positivity

lemma hardCubic_endpoints : hardCubic 0 = 2392 ∧ hardCubic 1 = 10000 := by
  norm_num [hardCubic]

private lemma integral_const_times_id (c a b : ℝ) :
    (∫ u in a..b, c * u) = c * ((b ^ 2 - a ^ 2) / 2) := by
  rw [intervalIntegral.integral_const_mul, integral_id]

lemma integral_hardCubic_sq (a b : ℝ) :
    (∫ u in a..b, hardCubic u ^ 2) =
      (21780889 / 7) * (b ^ 7 - a ^ 7) - 12563564 * (b ^ 6 - a ^ 6) +
      (168054454 / 5) * (b ^ 5 - a ^ 5) - 38904914 * (b ^ 4 - a ^ 4) +
      (82738705 / 3) * (b ^ 3 - a ^ 3) + 26352664 * (b ^ 2 - a ^ 2) +
      5721664 * (b - a) := by
  have he : (fun u => hardCubic u ^ 2) = fun u =>
      21780889 * u ^ 6 - 75381384 * u ^ 5 + 168054454 * u ^ 4 -
      155619656 * u ^ 3 + 82738705 * u ^ 2 + 52705328 * u + 5721664 := by
    funext u
    unfold hardCubic
    ring
  rw [he]
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_pow, integral_const_times_id, smul_eq_mul]
  norm_num
  ring

lemma hardCubicNorm_integral : (∫ u in (0 : ℝ)..1, hardCubic u ^ 2) = hardCubicNorm := by
  rw [integral_hardCubic_sq, hardCubicNorm_eq]
  norm_num

noncomputable def hardCubicShiftQuotient (v : ℝ) : ℝ :=
  -(239589779 / 70) * v ^ 6 + 9217325 * v ^ 5 - (147536616 / 5) * v ^ 4 +
  49600525 * v ^ 3 - (434463325 / 6) * v ^ 2 + (428544696 / 5) * v + 5721664

lemma integral_hardCubic_difference (v a b : ℝ) :
    (∫ u in a..b, (hardCubic u - hardCubic (u - v)) ^ 2) =
      (196028001 * v ^ 2) * (b ^ 5 - a ^ 5) / 5 +
      (-392056002 * v ^ 3 - 452288304 * v ^ 2) * (b ^ 4 - a ^ 4) / 4 +
      (326713335 * v ^ 4 + 678432456 * v ^ 3 + 569385138 * v ^ 2) *
        (b ^ 3 - a ^ 3) / 3 +
      (-130685334 * v ^ 5 - 376906920 * v ^ 4 - 569385138 * v ^ 3 -
        355893168 * v ^ 2) * (b ^ 2 - a ^ 2) / 2 +
      (21780889 * v ^ 6 + 75381384 * v ^ 5 + 168054454 * v ^ 4 +
        177946584 * v ^ 3 + 121374289 * v ^ 2) * (b - a) := by
  have he : (fun u => (hardCubic u - hardCubic (u - v)) ^ 2) = fun u =>
      (196028001 * v ^ 2) * u ^ 4 +
      (-392056002 * v ^ 3 - 452288304 * v ^ 2) * u ^ 3 +
      (326713335 * v ^ 4 + 678432456 * v ^ 3 + 569385138 * v ^ 2) * u ^ 2 +
      (-130685334 * v ^ 5 - 376906920 * v ^ 4 - 569385138 * v ^ 3 -
        355893168 * v ^ 2) * u +
      (21780889 * v ^ 6 + 75381384 * v ^ 5 + 168054454 * v ^ 4 +
        177946584 * v ^ 3 + 121374289 * v ^ 2) := by
    funext u
    unfold hardCubic
    ring
  rw [he]
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow, integral_const_times_id, smul_eq_mul]
  norm_num
  ring

/-- The inner energy including the hard endpoint jump. -/
lemma hardCubic_split_shift (v : ℝ) :
    (∫ u in v..1, (hardCubic u - hardCubic (u - v)) ^ 2) +
      (∫ u in 0..v, hardCubic u ^ 2) = v * hardCubicShiftQuotient v := by
  rw [integral_hardCubic_difference, integral_hardCubic_sq]
  unfold hardCubicShiftQuotient
  ring

lemma hardCubicEnergy_integral :
    (∫ v in (0 : ℝ)..1, hardCubicShiftQuotient v) = hardCubicEnergy := by
  unfold hardCubicShiftQuotient
  simp (discharger := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      integral_pow, integral_const_times_id, smul_eq_mul]
  rw [hardCubicEnergy_eq]
  norm_num

/-- The continuous energy integral, with the removable singularity at v=0
  handled on the actual integration interval rather than by pointwise division. -/
lemma hardCubicEnergy_double_integral :
    (∫ v in (0 : ℝ)..1,
      ((∫ u in v..1, (hardCubic u - hardCubic (u - v)) ^ 2) +
        (∫ u in 0..v, hardCubic u ^ 2)) / v) = hardCubicEnergy := by
  calc
    _ = ∫ v in (0 : ℝ)..1, hardCubicShiftQuotient v := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v hv
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
      have hv0 : v ≠ 0 := (Set.mem_Ioc.mp hv).1.ne'
      rw [hardCubic_split_shift]
      field_simp
    _ = _ := hardCubicEnergy_integral

lemma log_four_thirds_lt_hardCubic_budget : log (4 / 3 : ℝ) < 2877 / 10000 := by
  have hh := sum_range_sub_log_div_le (x := (1 / 7 : ℝ)) (by norm_num) 3
  norm_num [sum_range_succ] at hh
  have hu := (abs_le.mp hh).2
  linarith

/-- The exact continuous cubic ratio is below the threshold suggested by
  the reciprocal tail at cutoff exponent 3/4. This is not a sieve theorem. -/
lemma hardCubic_ratio_threshold :
    hardCubicEnergy / hardCubicNorm < 1 - log (4 / 3 : ℝ) := by
  have hn : 0 < hardCubicNorm := by rw [hardCubicNorm_eq]; norm_num
  have hm := hardCubic_margin_pos
  have hl := mul_lt_mul_of_pos_right log_four_thirds_lt_hardCubic_budget hn
  apply (div_lt_iff₀ hn).mpr
  nlinarith only [hm, hl]

/-- This particular profile does not meet the corresponding quadratic
  threshold. No impossibility statement about other sieve methods is made. -/
lemma hardCubic_not_quadratic_threshold :
    ¬hardCubicEnergy / hardCubicNorm < 1 - log (2 : ℝ) := by
  have hr : (1 / 2 : ℝ) < hardCubicEnergy / hardCubicNorm := by
    rw [hardCubicNorm_eq, hardCubicEnergy_eq]
    norm_num
  have hl := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hl
  linarith

#print axioms hardCubic_not_quadratic_threshold
#print axioms hardCubicEnergy_double_integral
#print axioms hardCubic_ratio_threshold
#print axioms hardCubicNorm_integral
#print axioms hardCubic_split_shift
#print axioms hardCubicEnergy_integral
#print axioms hardCubic_margin_pos
#print axioms hardCubic_positive
end Erdos970.FiniteSelberg
