import Submission.ChebyshevPNT

/-!
A diagnostic for attempts to use a bounded-function dilated-correlation
criterion directly with the unbounded von Mangoldt function. This file does
not prove or disprove Erdos 972.
-/
namespace Erdos972DilatedMangoldtObstruction

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction ArithmeticFunction.Moebius Topology

lemma distinct_prime_dilates_vanish {r s n : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (hn : n ≠ 1) :
    Λ (r * n) * Λ (s * n) = 0 := by
  by_contra h
  have hrn := vonMangoldt_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1
  have hsn := vonMangoldt_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2
  have hp := Nat.minFac_prime hn
  have hpr : n.minFac = r :=
    (isPrimePow_iff_unique_prime_dvd.mp hrn).unique
      ⟨hp, (Nat.minFac_dvd n).trans (dvd_mul_left n r)⟩
      ⟨hr, dvd_mul_right r n⟩
  have hps : n.minFac = s :=
    (isPrimePow_iff_unique_prime_dvd.mp hsn).unique
      ⟨hp, (Nat.minFac_dvd n).trans (dvd_mul_left n s)⟩
      ⟨hs, dvd_mul_right s n⟩
  exact hrs (hpr.symm.trans hps)

lemma sum_distinct_prime_dilates {r s N : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (hN : 1 ≤ N) :
    (∑ n ∈ Ioc 0 N, Λ (r * n) * Λ (s * n)) =
      Real.log r * Real.log s := by
  rw [sum_eq_single 1]
  · simp [vonMangoldt_apply_prime hr, vonMangoldt_apply_prime hs]
  · intro n _ hn
    exact distinct_prime_dilates_vanish hr hs hrs hn
  · simp [mem_Ioc, hN]

lemma distinct_prime_dilates_mean_tendsto {r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, Λ (r * n) * Λ (s * n)) / N) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (Real.log r * Real.log s) / N)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [sum_distinct_prime_dilates hr hs hrs hN]

lemma moebius_mul_mangoldt (n : ℕ) :
    (μ n : ℝ) * Λ n = if n.Prime then -Real.log n else 0 := by
  by_cases hn : n.Prime
  · simp [hn, moebius_apply_prime hn, vonMangoldt_apply_prime hn]
  · rw [if_neg hn]
    by_cases hp : IsPrimePow n
    · simp [moebius_apply_isPrimePow_not_prime hp hn]
    · simp [vonMangoldt_eq_zero_iff.mpr hp]

lemma moebius_mangoldt_sum (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (μ n : ℝ) * Λ n) = -Chebyshev.theta N := by
  simp_rw [moebius_mul_mangoldt]
  simp only [Chebyshev.theta, Nat.floor_natCast, sum_filter, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

lemma moebius_mangoldt_mean_tendsto :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, (μ n : ℝ) * Λ n) / N)
      atTop (𝓝 (-1)) := by
  simp_rw [moebius_mangoldt_sum, neg_div]
  exact (Erdos972ChebyshevPNT.theta_div_self_tendsto.comp
    tendsto_natCast_atTop_atTop).neg

#print axioms distinct_prime_dilates_vanish
#print axioms distinct_prime_dilates_mean_tendsto
#print axioms moebius_mangoldt_mean_tendsto

end Erdos972DilatedMangoldtObstruction
