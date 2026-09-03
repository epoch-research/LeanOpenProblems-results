import FormalConjecturesUtil

/-! Cesàro convergence implies convergence of the corresponding logarithmic means.
This is a summability lemma, not a prime-pair lower bound. -/
namespace Erdos972CesaroLogarithmicMean

open Finset Filter Asymptotics
open scoped Topology

lemma harmonic_real_eq (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ range N, (1 : ℝ) / (k + 1) := by
  simp [harmonic, one_div]

lemma harmonic_real_tendsto :
    Tendsto (fun N : ℕ => (harmonic N : ℝ)) atTop atTop := by
  simpa only [harmonic_real_eq] using Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- Weighted means of a convergent sequence have the same limit when the
nonnegative weights have divergent total mass. -/
lemma weighted_mean {u w : ℕ → ℝ} {L : ℝ}
    (hu : Tendsto u atTop (𝓝 L)) (hw : ∀ n, 0 ≤ w n)
    (hW : Tendsto (fun N => ∑ n ∈ range N, w n) atTop atTop) :
    Tendsto (fun N => (∑ n ∈ range N, u n * w n) /
      (∑ n ∈ range N, w n)) atTop (𝓝 L) := by
  have hsmall : (fun n => (u n - L) * w n) =o[atTop] w := by
    have h := ((isLittleO_one_iff ℝ).mpr (tendsto_sub_nhds_zero_iff.mpr hu)).mul_isBigO
      (isBigO_refl w atTop)
    simpa only [one_mul] using h
  have hs := (hsmall.sum_range hw hW).tendsto_div_nhds_zero
  rw [← tendsto_sub_nhds_zero_iff]
  apply hs.congr'
  filter_upwards [hW.eventually_gt_atTop 0] with N hN
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, sub_div]
  rw [mul_div_cancel_right₀ _ hN.ne']

lemma tail_harmonic_identity (N : ℕ) :
    (∑ k ∈ range N, (1 : ℝ) / (k + 2)) = (harmonic (N+1) : ℝ) - 1 := by
  rw [harmonic_real_eq, sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one]
  simp_rw [show ∀ k : ℕ, (k : ℝ) + 1 + 1 = k + 2 by intro k; ring]
  ring

lemma tail_harmonic_tendsto :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, (1 : ℝ) / (k+2)) atTop atTop := by
  simp only [tail_harmonic_identity]
  simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
    ((tendsto_add_atTop_iff_nat 1).mpr harmonic_real_tendsto)

lemma logarithmic_abel (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range (N+1), a k / (k+1)) =
      (∑ k ∈ range (N+1), a k) / (N+1) +
        ∑ k ∈ range N, ((∑ j ∈ range (k+1), a j) / (k+1)) *
          ((1 : ℝ) / (k+2)) := by
  have h := sum_range_by_parts (fun k : ℕ => (1 : ℝ)/(k+1)) a (N+1)
  simp only [add_tsub_cancel_right, smul_eq_mul, one_div_mul_eq_div] at h
  rw [h, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Ordinary Cesàro convergence transfers to reciprocal-weighted means.
The reciprocal weight is on the input index, not on a damping parameter. -/
theorem cesaro_to_logarithmic {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ k ∈ range N, a k) / N) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, a k / (k+1)) /
      (harmonic N : ℝ)) atTop (𝓝 L) := by
  let u : ℕ → ℝ := fun N => (∑ k ∈ range (N+1), a k) / (N+1)
  let W : ℕ → ℝ := fun N => ∑ k ∈ range N, (1 : ℝ)/(k+2)
  have hu : Tendsto u atTop (𝓝 L) := by
    simpa only [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).mpr ha
  have hW : Tendsto W atTop atTop := tail_harmonic_tendsto
  have hH : Tendsto (fun N : ℕ => (harmonic (N+1) : ℝ)) atTop atTop :=
    (tendsto_add_atTop_iff_nat 1).mpr harmonic_real_tendsto
  have hratio : Tendsto (fun N => W N / (harmonic (N+1) : ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_nhds.div_atTop hH : Tendsto
        (fun N : ℕ => (1 : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0))
    simp only [sub_zero] at hh
    apply hh.congr'
    filter_upwards [hH.eventually_gt_atTop 0] with N hN
    dsimp [W]
    rw [tail_harmonic_identity, sub_div, div_self hN.ne']
  have hmean := weighted_mean hu (fun n : ℕ => by positivity : ∀ n : ℕ, 0 ≤ (1 : ℝ)/(n+2)) hW
  have hmain := hmean.mul hratio
  simp only [mul_one] at hmain
  have hboundary := hu.div_atTop hH
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hlim := hboundary.add hmain
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hW.eventually_gt_atTop 0] with N hN
  rw [logarithmic_abel, add_div]
  dsimp only [u] at *
  congr 1
  rw [div_mul_div_cancel₀ hN.ne']

lemma harmonic_div_log_tendsto :
    Tendsto (fun N : ℕ => (harmonic N : ℝ) / Real.log N) atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_harmonic_sub_log.div_atTop hlog
  have hlim := hh.add_const 1
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with N hN
  rw [sub_div, div_self hN.ne', sub_add_cancel]

/-- The usual normalization by `log N` is equivalent to harmonic normalization. -/
theorem cesaro_to_logarithmic_log {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ k ∈ range N, a k) / N) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, a k / (k+1)) /
      Real.log N) atTop (𝓝 L) := by
  have hh := (cesaro_to_logarithmic ha).mul harmonic_div_log_tendsto
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [harmonic_real_tendsto.eventually_gt_atTop 0] with N hN
  rw [div_mul_div_cancel₀ hN.ne']

lemma sum_Ioc_eq_sum_range_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = ∑ n ∈ range N, f (n+1) := by
  simpa only [Nat.Ico_zero_eq_range, Ico_add_one_add_one_eq_Ioc] using
    (sum_Ico_add' f 0 N 1).symm

/-- Positive-index form, suitable for arithmetic functions. -/
theorem cesaro_Ioc_to_logarithmic {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ k ∈ Ioc 0 N, a k) / N) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ k ∈ Ioc 0 N, a k / k) /
      Real.log N) atTop (𝓝 L) := by
  simp only [sum_Ioc_eq_sum_range_succ] at ha ⊢
  simpa only [Nat.cast_add, Nat.cast_one] using cesaro_to_logarithmic_log ha

#print axioms cesaro_to_logarithmic
#print axioms cesaro_Ioc_to_logarithmic

end Erdos972CesaroLogarithmicMean
