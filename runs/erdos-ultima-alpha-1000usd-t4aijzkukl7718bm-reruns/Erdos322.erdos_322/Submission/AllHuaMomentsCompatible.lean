import Submission.PositivePrimitiveScalingFiniteMoments

/-! The entire available Hua-type moment family, not just finitely many
moments, is compatible with power peaks for abstract positive counts having
exact fourth-power primitive scaling. This is NOT a disproof of Erdős 322. -/
namespace Erdos322Research.AllHuaMomentsCompatible
noncomputable section
open Finset Erdos322.MomentReduction ScalingFiniteMoments PrimitiveScalingFiniteMoments
  PositivePrimitiveScalingFiniteMoments
set_option Elab.async false
set_option maxHeartbeats 0

/-- A pointwise bound for the fixed model with primitive spikes at fifth
powers of primes and fourth-power scaling. -/
lemma model_pointwise (n : ℕ) (hn : 1 ≤ n) :
    (positiveFull 4 5 n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
  have hnp : 0 < n := by omega
  have hdiv := (Finset.mem_filter.mp (maximalPowerDivisor_mem 5 n hnp)).2
  have hp : maximalPowerDivisor 5 n ^ 5 ≤ n := Nat.le_of_dvd hnp hdiv
  have hroot : (maximalPowerDivisor 5 n : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) := by
    calc
      (maximalPowerDivisor 5 n : ℝ) =
          ((maximalPowerDivisor 5 n : ℝ) ^ 5) ^ (1 / 5 : ℝ) := by
        simpa only [one_div] using (Real.pow_rpow_inv_natCast
          (Nat.cast_nonneg (maximalPowerDivisor 5 n) : (0 : ℝ) ≤ maximalPowerDivisor 5 n)
          (by decide : 5 ≠ 0)).symm
      _ ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hp) (by norm_num)
  have hsp : (fullSpike 4 5 n : ℝ) ≤ maximalPowerDivisor 5 n := by
    exact_mod_cast fullSpike_le_maximalPowerDivisor 4 5 n (by decide) (by decide)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  simp only [positiveFull, positiveBaseline, if_neg hnp.ne', Nat.cast_add, Nat.cast_one]
  linarith

/-- This one fixed model satisfies a bound for EVERY moment order. -/
theorem model_all_moments :
    ∀ q : ℕ, ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (positiveFull 4 5) (q + 2) N ≤ C * (N : ℝ) ^ (1 + (q : ℝ) / 5) := by
  obtain ⟨A, hA, hlow⟩ := two_sided_low_moments 4 5 2 (by decide) (by decide) (by decide)
  intro q
  refine ⟨2 ^ q * A, by positivity, fun N hN ↦ ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hpoint (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      (positiveFull 4 5 n : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    exact (model_pointwise n (Finset.mem_Icc.mp hn).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
          (by norm_num)) (by norm_num))
  have hm : countMoment (positiveFull 4 5) (q + 2) N ≤
      (2 * (N : ℝ) ^ (1 / 5 : ℝ)) ^ q * countMoment (positiveFull 4 5) 2 N := by
    unfold countMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (hpoint n hn) q) (by positivity)
  calc
    countMoment (positiveFull 4 5) (q + 2) N ≤
        (2 * (N : ℝ) ^ (1 / 5 : ℝ)) ^ q * (A * N) :=
      hm.trans (mul_le_mul_of_nonneg_left (hlow 2 (by decide) N).2 (by positivity))
    _ = (2 ^ q * A) * (N : ℝ) ^ (1 + (q : ℝ) / 5) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hNp.le]
      have he : (1 / 5 : ℝ) * (q : ℝ) = (q : ℝ) / 5 := by ring
      rw [he, Real.rpow_add hNp, Real.rpow_one]
      ring

/-- In particular all the current quartic Hua exponents hold simultaneously,
even without an epsilon loss. -/
theorem model_hua_moments :
    ∀ q : ℕ, ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
      countMoment (positiveFull 4 5) (q + 2) N ≤ C * (N : ℝ) ^ (5 / 4 + (q : ℝ) / 2) := by
  intro q
  obtain ⟨C, hC, hb⟩ := model_all_moments q
  refine ⟨C, hC, fun N hN ↦ (hb N hN).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  linarith

/-- A complete abstract witness showing that the infinite Hua moment family,
a linear first moment, positivity, and exact primitive scaling do not by
themselves rule out polynomial peaks. It is not the representation count. -/
theorem hua_family_with_exact_scaling_and_peaks :
    ∃ f g : ℕ → ℕ,
      (∀ n, f n = ∑ b ∈ n.divisors.filter (fun b ↦ b ^ 4 ∣ n), g (n / b ^ 4)) ∧
      (∀ n s, 0 < s → f n ≤ f (n * s ^ 4)) ∧
      (∀ n, g n ≤ f n) ∧
      (∀ n, 0 < n → 1 ≤ f n) ∧
      (∃ A > (0 : ℝ), ∀ N : ℕ, countMoment f 1 N ≤ A * N) ∧
      (∀ q : ℕ, ∃ C > (0 : ℝ), ∀ N : ℕ, 1 ≤ N →
        countMoment f (q + 2) N ≤ C * (N : ℝ) ^ (5 / 4 + (q : ℝ) / 2)) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < (g n : ℝ)}.Infinite) ∧
      (∃ c > (0 : ℝ), {n : ℕ | (n : ℝ) ^ c < (f n : ℝ)}.Infinite) := by
  refine ⟨positiveFull 4 5, positivePrimitive 4 5,
    (fun n ↦ exact_scaling 4 5 n (by decide)),
    (fun n s hs ↦ power_scaling_monotone 4 5 n s (by decide) hs),
    primitive_le_full 4 5, full_pos 4 5, ?_, model_hua_moments,
    primitive_peaks 4 5 (by decide), full_peaks 4 5 (by decide)⟩
  obtain ⟨A, hA, hlow⟩ := two_sided_low_moments 4 5 1 (by decide) (by decide) (by decide)
  exact ⟨A, hA, fun N ↦ (hlow 1 (by decide) N).2⟩

end
end Erdos322Research.AllHuaMomentsCompatible
