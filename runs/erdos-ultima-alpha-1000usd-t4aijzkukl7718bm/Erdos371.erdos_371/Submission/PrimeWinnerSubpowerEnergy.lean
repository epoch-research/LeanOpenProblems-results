import Submission.PrimeWinnerFlux

/-! A subpower loss in the prime-winner energy would still suffice. The
energy hypothesis below remains unproved. -/

namespace Erdos371

open Finset Filter
open scoped Topology

noncomputable def primeWinnerLowSum (B N : ℕ) : ℝ :=
  ∑ p ∈ (primeWinnerLabels N).filter (· ≤ B), primeWinnerSum p N

lemma primeWinnerLowSum_sq_le (B N : ℕ) :
    (primeWinnerLowSum B N)^2 ≤ (B + 1 : ℝ) * primeWinnerEnergy N := by
  let S := (primeWinnerLabels N).filter (· ≤ B)
  have hc : S.card ≤ B + 1 := by
    apply (card_le_card (show S ⊆ range (B + 1) from ?_)).trans_eq (card_range _)
    intro p hp
    exact mem_range.mpr (by have := (mem_filter.mp hp).2; omega)
  have he : (∑ p ∈ S, (primeWinnerSum p N)^2) ≤ primeWinnerEnergy N := by
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
  have hh := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun p => primeWinnerSum p N)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hh
  exact hh.trans (mul_le_mul (by exact_mod_cast hc) he (by positivity) (by positivity))

lemma signedCount_norm_le_low_add_high (B N : ℕ) :
    ‖(risingCount N : ℝ) - fallingCount N‖ ≤
      ‖primeWinnerLowSum B N‖ + primeWinnerL1Above B N := by
  have he : (risingCount N : ℝ) - fallingCount N = primeWinnerLowSum B N +
      ∑ p ∈ (primeWinnerLabels N).filter (B < ·), primeWinnerSum p N := by
    rw [← primeWinnerSum_total]
    unfold primeWinnerLowSum
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases h : p ≤ B <;> simp [h, lt_iff_not_ge]
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)

/-- The low-prime part has zero normalized mean under a slightly superlinear
energy bound, once a fixed top power band has been removed. -/
lemma primeWinnerLowSum_power_tendsto (u : ℝ) (hu0 : 0 < u) (hu : u ≤ 1 / 8)
    (hE : ∀ᶠ N : ℕ in atTop, primeWinnerEnergy N ≤ (N : ℝ) ^ (1 + u / 2)) :
    Tendsto (fun N : ℕ => primeWinnerLowSum ⌈(N : ℝ) ^ (1 - u)⌉₊ N / N)
      atTop (nhds 0) := by
  have ht1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-u / 2)) atTop (nhds 0) := by
    simpa only [neg_div] using (tendsto_rpow_neg_atTop (half_pos hu0)).comp tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-1 + u / 2)) atTop (nhds 0) := by
    have he : -1 + u / 2 = -(1 - u / 2) := by ring
    rw [he]
    exact (tendsto_rpow_neg_atTop (show 0 < 1 - u / 2 by linarith)).comp
      tendsto_natCast_atTop_atTop
  have ht := (ht1.add (ht2.const_mul 2)).sqrt
  simp only [mul_zero, add_zero, Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hE, eventually_gt_atTop (0 : ℕ)] with N hEN hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hceil : (⌈(N : ℝ) ^ (1 - u)⌉₊ : ℝ) + 1 ≤ (N : ℝ) ^ (1 - u) + 2 := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) (1 - u))
    linarith
  have hs := (primeWinnerLowSum_sq_le ⌈(N : ℝ) ^ (1 - u)⌉₊ N).trans
    (mul_le_mul hceil hEN (by unfold primeWinnerEnergy; positivity) (by positivity))
  have hpow1 : (N : ℝ) ^ (1 - u) * (N : ℝ) ^ (1 + u / 2) / (N : ℝ)^2 =
      (N : ℝ) ^ (-u / 2) := by
    rw [← Real.rpow_add hN', ← Real.rpow_two, ← Real.rpow_sub hN']
    congr 1
    ring
  have hpow2 : (N : ℝ) ^ (1 + u / 2) / (N : ℝ)^2 = (N : ℝ) ^ (-1 + u / 2) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hN']
    congr 1
    ring
  have hpow : (((N : ℝ) ^ (1 - u) + 2) * (N : ℝ) ^ (1 + u / 2)) / (N : ℝ)^2 =
      (N : ℝ) ^ (-u / 2) + 2 * (N : ℝ) ^ (-1 + u / 2) := by
    calc
      _ = (N : ℝ) ^ (1 - u) * (N : ℝ) ^ (1 + u / 2) / (N : ℝ)^2 +
          2 * ((N : ℝ) ^ (1 + u / 2) / (N : ℝ)^2) := by ring
      _ = _ := by rw [hpow1, hpow2]
  apply Real.le_sqrt_of_sq_le
  rw [norm_div, Real.norm_natCast, div_pow, Real.norm_eq_abs, sq_abs, ← hpow]
  exact div_le_div_of_nonneg_right hs (sq_nonneg (N : ℝ))

open FiniteSieve in
/-- A subpower-loss energy estimate suffices for the original conjecture.
The hypothesis is a substantive unproved arithmetic assertion. -/
theorem density_of_subpower_primeWinnerEnergy
    (hE : ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      primeWinnerEnergy N ≤ (N : ℝ) ^ (1 + η)) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) := by
  rw [density_iff_signed_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hden : 0 < 4 * (largePairConstant + 1) := by positivity
  let u : ℝ := min (1 / 8) (ε / (4 * (largePairConstant + 1)))
  have hu0 : 0 < u := lt_min (by norm_num) (div_pos hε hden)
  have hu : u ≤ 1 / 8 := min_le_left _ _
  have huε : u * (4 * (largePairConstant + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have husq : u^2 ≤ u := by nlinarith [hu0.le]
  have hcu : largePairConstant * u^2 ≤ ε / 4 := by
    have hh := mul_le_mul_of_nonneg_left husq hC
    nlinarith [hu0.le]
  have hlow := primeWinnerLowSum_power_tendsto u hu0 hu (hE (u / 2) (half_pos hu0))
  have hhigh := primeWinnerL1Above_top_eventually_le (fun N => ⌈(N : ℝ) ^ (1 - u)⌉₊)
    u hu0.le hu (Eventually.of_forall fun N => Nat.le_ceil _) (ε / 4) (by positivity)
  have hl := (Metric.tendsto_nhds.mp hlow) (ε / 4) (by positivity)
  filter_upwards [hl, hhigh] with N hlN hhN
  simp only [dist_zero_right] at hlN ⊢
  have hb := div_le_div_of_nonneg_right
    (signedCount_norm_le_low_add_high ⌈(N : ℝ) ^ (1 - u)⌉₊ N) (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hb
  have hn (x : ℝ) : ‖x‖ / (N : ℝ) = ‖x / N‖ := by
    rw [norm_div, Real.norm_natCast]
  rw [hn, hn] at hb
  linarith

#print axioms primeWinnerLowSum_sq_le
#print axioms primeWinnerLowSum_power_tendsto
#print axioms density_of_subpower_primeWinnerEnergy

end Erdos371
