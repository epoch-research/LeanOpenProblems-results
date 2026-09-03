import Submission.RatioNearTieDensity

/-! Consequences of fixed-ratio near-tie rarity: bounded multiplicative
perturbations preserve the density question, and a rational kernel approximates
the comparison sign in Cesàro mean. No cancellation of that kernel is asserted. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

/-- Bounded positive multiplicative changes to the two prime factors leave
all possible comparison densities unchanged. -/
theorem bounded_multiplicative_perturbation_density_iff (C : ℕ) (a b : ℕ → ℕ)
    (ha : ∀ n, 1 ≤ a n ∧ a n ≤ C) (hb : ∀ n, 1 ≤ b n ∧ b n ≤ C) (d : ℝ) :
    {n | a n * Nat.maxPrimeFac n < b n * Nat.maxPrimeFac (n+1)}.HasDensity d ↔
      {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity d := by
  classical
  apply density_iff_of_exception _ _ (factorRatioEvent C)
  · intro n hn
    have hC : 1 ≤ C := (ha n).1.trans (ha n).2
    have hp : Nat.maxPrimeFac n ≤ C * Nat.maxPrimeFac n := by nlinarith
    have hq : Nat.maxPrimeFac (n+1) ≤ C * Nat.maxPrimeFac (n+1) := by nlinarith
    have hp' : Nat.maxPrimeFac n ≤ a n * Nat.maxPrimeFac n := by
      nlinarith [(ha n).1]
    have hq' : Nat.maxPrimeFac (n+1) ≤ b n * Nat.maxPrimeFac (n+1) := by
      nlinarith [(hb n).1]
    have hp'' := Nat.mul_le_mul_right (Nat.maxPrimeFac n) (ha n).2
    have hq'' := Nat.mul_le_mul_right (Nat.maxPrimeFac (n+1)) (hb n).2
    unfold factorRatioEvent at hn
    push_neg at hn
    by_cases h : Nat.maxPrimeFac n ≤ C * Nat.maxPrimeFac (n+1)
    · have hfar := hn h
      constructor <;> intro _ <;> omega
    · have hfar : C * Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n := by omega
      constructor <;> intro _ <;> omega
  · exact factorRatioEvent_hasDensity_zero C

noncomputable def rationalFactorSign (n : ℕ) : ℝ :=
  ((Nat.maxPrimeFac (n+1) : ℝ) - Nat.maxPrimeFac n) /
    ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n)

lemma pairPrimeFactor_sum_pos (n : ℕ) :
    (0 : ℝ) < (Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n := by
  have hq : 0 < Nat.maxPrimeFac (n+1) := by
    by_cases hn : n = 0
    · subst n; simp
    · have := (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)).pos
      exact this
  positivity

lemma rationalFactorSign_error_eq (n : ℕ) :
    |factorSign n - rationalFactorSign n| =
      2 * min (Nat.maxPrimeFac n : ℝ) (Nat.maxPrimeFac (n+1) : ℝ) /
        ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n) := by
  have hden := pairPrimeFactor_sum_pos n
  unfold factorSign predicateSign rationalFactorSign
  split_ifs with h
  · have h' : (Nat.maxPrimeFac n : ℝ) < Nat.maxPrimeFac (n+1) := by exact_mod_cast h
    rw [min_eq_left h'.le]
    have he : 1 - ((Nat.maxPrimeFac (n+1) : ℝ) - Nat.maxPrimeFac n) /
        ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n) =
      2 * Nat.maxPrimeFac n / ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n) := by
      field_simp; ring
    rw [he, abs_of_nonneg (by positivity)]
  · have h' : (Nat.maxPrimeFac (n+1) : ℝ) ≤ Nat.maxPrimeFac n := by exact_mod_cast (not_lt.mp h)
    rw [min_eq_right h']
    have he : -1 - ((Nat.maxPrimeFac (n+1) : ℝ) - Nat.maxPrimeFac n) /
        ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n) =
      -(2 * Nat.maxPrimeFac (n+1) / ((Nat.maxPrimeFac (n+1) : ℝ) + Nat.maxPrimeFac n)) := by
      field_simp; ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]

lemma rationalFactorSign_error_le_two (n : ℕ) :
    |factorSign n - rationalFactorSign n| ≤ 2 := by
  rw [rationalFactorSign_error_eq]
  apply (div_le_iff₀ (pairPrimeFactor_sum_pos n)).mpr
  have h := min_le_left (Nat.maxPrimeFac n : ℝ) (Nat.maxPrimeFac (n+1) : ℝ)
  have hq : (0 : ℝ) ≤ Nat.maxPrimeFac (n+1) := Nat.cast_nonneg _
  linarith

lemma rationalFactorSign_error_le_of_not_ratio (C n : ℕ)
    (hn : ¬factorRatioEvent C n) :
    |factorSign n - rationalFactorSign n| ≤ 2 / (C+1 : ℝ) := by
  rw [rationalFactorSign_error_eq]
  have hden := pairPrimeFactor_sum_pos n
  have hC : (0 : ℝ) < C+1 := by positivity
  apply (div_le_div_iff₀ hden hC).mpr
  unfold factorRatioEvent at hn
  push_neg at hn
  by_cases h : Nat.maxPrimeFac n ≤ C * Nat.maxPrimeFac (n+1)
  · have hf : (C : ℝ)*Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by exact_mod_cast hn h
    have hp := min_le_left (Nat.maxPrimeFac n : ℝ) (Nat.maxPrimeFac (n+1) : ℝ)
    have he := mul_le_mul_of_nonneg_right hp hC.le
    nlinarith
  · have hf : (C : ℝ)*Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n := by exact_mod_cast (lt_of_not_ge h)
    have hq := min_le_right (Nat.maxPrimeFac n : ℝ) (Nat.maxPrimeFac (n+1) : ℝ)
    have he := mul_le_mul_of_nonneg_right hq hC.le
    nlinarith

lemma rationalFactorSign_error_sum_bound (C N : ℕ) :
    (∑ n ∈ range N, |factorSign n - rationalFactorSign n|) ≤
      2 * (((range N).filter (factorRatioEvent C)).card : ℝ) +
        N * (2 / (C+1 : ℝ)) := by
  classical
  have hp (n : ℕ) : |factorSign n - rationalFactorSign n| ≤
      (if factorRatioEvent C n then (2 : ℝ) else 0) + 2/(C+1 : ℝ) := by
    by_cases hn : factorRatioEvent C n
    · rw [if_pos hn]
      exact (rationalFactorSign_error_le_two n).trans (le_add_of_nonneg_right (by positivity))
    · simpa only [if_neg hn, zero_add] using rationalFactorSign_error_le_of_not_ratio C n hn
  have hsum := sum_le_sum (s := range N) (fun n _ => hp n)
  simpa only [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const,
    card_range, nsmul_eq_mul, mul_comm] using hsum

/-- The rational kernel and the discrete sign have vanishing mean absolute
error. This does not yet prove that either signed mean tends to zero. -/
theorem rationalFactorSign_mean_error_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, |factorSign n - rationalFactorSign n|) / N)
      atTop (nhds 0) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C : ℕ, hC⟩ := exists_nat_gt (4/ε)
  have hCpos : (0 : ℝ) < C+1 := by positivity
  have hsmall : 2/(C+1 : ℝ) < ε/2 := by
    apply (div_lt_iff₀ hCpos).mpr
    have he := (div_lt_iff₀ hε).mp hC
    nlinarith
  have hD := (density_iff_count _ 0).mp (factorRatioEvent_hasDensity_zero C)
  have ht := hD.const_mul 2
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε/2 by linarith)),
    eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hz : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hb := div_le_div_of_nonneg_right (rationalFactorSign_error_sum_bound C N) (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div, mul_div_assoc, mul_div_cancel_left₀ _ hz] at hb
  linarith

#print axioms bounded_multiplicative_perturbation_density_iff
#print axioms rationalFactorSign_mean_error_tendsto_zero

lemma rationalFactorSign_average_difference_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, factorSign n) / N -
      (∑ n ∈ range N, rationalFactorSign n) / N) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => ?_) rationalFactorSign_mean_error_tendsto_zero
  rw [Real.norm_eq_abs, ← sub_div, ← sum_sub_distrib, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

lemma factorSign_sum_eq_count_difference (N : ℕ) :
    (∑ n ∈ range N, factorSign n) = (risingCount N : ℝ) - fallingCount N := by
  unfold factorSign
  rw [predicateSign_sum]
  change 2 * (risingCount N : ℝ) - N = _
  have hc : (risingCount N : ℝ) + fallingCount N = N := by
    exact_mod_cast comparison_count_partition N
  linarith

/-- An equivalent bounded rational-kernel cancellation problem. The limit on
the right remains to be proved. -/
theorem density_iff_rationalFactorSign_average :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (fun N : ℕ => (∑ n ∈ range N, rationalFactorSign n) / N)
        atTop (nhds 0) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  have he := rationalFactorSign_average_difference_tendsto_zero
  constructor
  · intro ht
    have h := ht.sub he
    simpa only [sub_self, sub_sub_cancel] using h
  · intro ht
    have h := he.add ht
    simpa only [add_zero, sub_add_cancel] using h

#print axioms density_iff_rationalFactorSign_average

end Erdos371
