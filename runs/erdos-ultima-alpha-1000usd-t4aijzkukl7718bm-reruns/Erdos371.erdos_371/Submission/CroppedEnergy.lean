import FormalConjecturesUtil
import Submission.ElementaryEnergy

/-! Removing the density-zero contribution of bounded winning cofactors gives
an improved conditional energy criterion. No `O(N log N)` estimate is asserted. -/

namespace Erdos371CroppedEnergy

open Erdos371PrimeDiscrepancy Erdos371PrimeEnergy Erdos371ElementaryEnergy
open Erdos371CofactorDensity Filter
open scoped Topology

noncomputable def badCount (K N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K).card : ℝ)

lemma badCount_mean_tendsto_zero (K : ℕ) :
    Tendsto (fun N => badCount K N / N) atTop (𝓝 0) := by
  have he (N : ℕ) :
      {n | n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K}.partialDensity Set.univ N =
      badCount K N / N := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hh : {n | n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K} ∩ Set.Iio N =
        ↑((Finset.range N).filter fun n => n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K) := by
      ext n
      simp [and_comm]
    rw [hh, Set.ncard_coe_finset]
    rfl
  have hh := bounded_cofactor_pair_hasDensity_zero K
  change Tendsto (fun N => {n | n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K}.partialDensity Set.univ N) _ _ at hh
  simpa only [he] using hh

lemma high_winner_bad {K N n : ℕ} (hK : 0 < K) (hn : n < N)
    (hw : N / K < winner n) : n / P n ≤ K ∨ (n+1) / P (n+1) ≤ K := by
  have hw0 : 0 < winner n := lt_of_le_of_lt (Nat.zero_le _) hw
  have hN : N < winner n * K := (Nat.div_lt_iff_lt_mul hK).mp hw
  have hdiv : N / winner n < K :=
    (Nat.div_lt_iff_lt_mul hw0).mpr (by simpa [Nat.mul_comm] using hN)
  by_cases hc : P n ≤ P (n+1)
  · right
    have he : winner n = P (n+1) := max_eq_right hc
    rw [he] at hdiv
    exact (Nat.div_le_div_right (show n+1 ≤ N by omega)).trans hdiv.le
  · left
    have he : winner n = P n := max_eq_left (Nat.le_of_not_ge hc)
    rw [he] at hdiv
    exact (Nat.div_le_div_right hn.le).trans hdiv.le

lemma high_groups_abs_le {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (∑ p ∈ ((N+1).primesBelow.filter fun p => N/K < p), |(group p N : ℝ)|) ≤
      badCount K N := by
  classical
  let s := (N+1).primesBelow.filter fun p => N/K < p
  calc
    _ ≤ ∑ p ∈ s, (((Finset.range N).filter fun n => winner n = p).card : ℝ) :=
      Finset.sum_le_sum (fun p _ => group_abs_le_count p N)
    _ = ∑ n ∈ Finset.range N, if winner n ∈ s then (1 : ℝ) else 0 := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ n ∈ Finset.range N,
        if n/P n ≤ K ∨ (n+1)/P (n+1) ≤ K then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hw : winner n ∈ s
      · have hb := high_winner_bad hK (Finset.mem_range.mp hn) (Finset.mem_filter.mp hw).2
        simp [hw, hb]
      · simp [hw]
        positivity
    _ = badCount K N := by simp [badCount]

lemma low_groups_sq_le {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (∑ p ∈ ((N+1).primesBelow.filter fun p => p ≤ N/K), (group p N : ℝ))^2 ≤
      Nat.primeCounting (N/K) * energy N := by
  let s := (N+1).primesBelow.filter fun p => p ≤ N/K
  have hs : s = (N/K+1).primesBelow := by
    ext p
    simp only [s, Finset.mem_filter, Nat.mem_primesBelow]
    have hd : N/K ≤ N := Nat.div_le_self _ _
    constructor
    · rintro ⟨⟨_, hp⟩, hb⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨hb, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  have hcard : (s.card : ℝ) = Nat.primeCounting (N/K) := by
    rw [hs, Nat.primesBelow_card_eq_primeCounting']
    rfl
  have hsum : (∑ p ∈ s, (group p N : ℝ)^2) ≤ energy N := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => sq_nonneg _)
  calc
    _ ≤ s.card * ∑ p ∈ s, (group p N : ℝ)^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (Nat.primeCounting (N/K) : ℝ) * energy N := by
      rw [hcard]
      exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)

lemma total_abs_cropped_bound {K N : ℕ} (hK : 0 < K) (hN : 0 < N) :
    |(total N : ℝ)| ≤ 1 + Real.sqrt (Nat.primeCounting (N/K) * energy N) + badCount K N := by
  classical
  have he : (total N : ℝ) = 1 +
      (∑ p ∈ ((N+1).primesBelow.filter fun p => p ≤ N/K), (group p N : ℝ)) +
      ∑ p ∈ ((N+1).primesBelow.filter fun p => N/K < p), (group p N : ℝ) := by
    rw [total_eq_prime_groups hN]
    push_cast
    rw [← Finset.sum_filter_add_sum_filter_not (s := (N+1).primesBelow)
      (p := fun p => p ≤ N/K)]
    simp [not_le, add_assoc]
  have hl : |∑ p ∈ ((N+1).primesBelow.filter fun p => p ≤ N/K), (group p N : ℝ)| ≤
      Real.sqrt (Nat.primeCounting (N/K) * energy N) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact low_groups_sq_le hK N
  have hh : |∑ p ∈ ((N+1).primesBelow.filter fun p => N/K < p), (group p N : ℝ)| ≤
      badCount K N := (Finset.abs_sum_le_sum_abs _ _).trans (high_groups_abs_le hK N)
  rw [he]
  calc
    _ ≤ |(1:ℝ)| + |∑ p ∈ ((N+1).primesBelow.filter fun p => p ≤ N/K), (group p N : ℝ)| +
        |∑ p ∈ ((N+1).primesBelow.filter fun p => N/K < p), (group p N : ℝ)| := by
      apply (abs_add_le _ _).trans
      exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by rw [abs_one]; linarith


lemma eventually_cropped_prime_counting_bound {K : ℕ} (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.primeCounting (N/K) : ℝ) * Real.log N / N ≤
        2 * (Real.log 4 + 1) / K := by
  have hb : ∀ᶠ m : ℕ in atTop,
      (Nat.primeCounting m : ℝ) ≤ (Real.log 4 + 1) * m / Real.log m := by
    simpa using (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hb' := (Nat.tendsto_div_const_atTop hK.ne').eventually hb
  filter_upwards [hb', eventually_ge_atTop (2*K^2+2)] with N hbN hN
  have hm : 2*K ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith)
  have hm1 : 1 < N/K := by omega
  have hN0 : 0 < N := by omega
  have hsq : N ≤ (N/K)^2 := by
    have hh := Nat.lt_mul_div_succ N hK
    nlinarith
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN0
  have hk : (0:ℝ) < K := Nat.cast_pos.mpr hK
  have hlogm : 0 < Real.log (N/K : ℕ) := Real.log_pos (by exact_mod_cast hm1)
  have hlog : Real.log (N:ℝ) ≤ 2 * Real.log (N/K : ℕ) := by
    have hh := Real.log_le_log hn (show (N:ℝ) ≤ ((N/K : ℕ):ℝ)^2 by exact_mod_cast hsq)
    simpa using hh
  have hmul : (Nat.primeCounting (N/K) : ℝ) * Real.log (N/K : ℕ) ≤
      (Real.log 4+1) * (N/K : ℕ) := (le_div_iff₀ hlogm).mp hbN
  have hC : 0 ≤ 2*(Real.log 4+1) := by positivity
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ (Nat.primeCounting (N/K) : ℝ) * (2 * Real.log (N/K : ℕ)) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ 2*(Real.log 4+1) * (N/K : ℕ) := by linarith
    _ ≤ 2*(Real.log 4+1) * ((N:ℝ)/K) := mul_le_mul_of_nonneg_left Nat.cast_div_le hC
    _ = 2*(Real.log 4+1)/K * N := by ring

/-- Bounded `energy / (N log N)` is enough after discarding bounded cofactors.
The energy bound remains an explicit, unproved hypothesis. -/
theorem density_half_of_eventually_n_log_energy {C : ℝ} (hC : 0 < C)
    (hE : ∀ᶠ N : ℕ in atTop, energy N ≤ C * N * Real.log N) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  apply density_half_iff_total_mean_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε/3 := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 * (Real.log 4+1) * C)
  obtain ⟨K, hK, hsmall⟩ := ((eventually_gt_atTop 0).and
    (ht.eventually_lt_const (sq_pos_of_pos he))).exists
  have hb := eventually_cropped_prime_counting_bound hK
  have hbad := (badCount_mean_tendsto_zero K).eventually_lt_const he
  have hrecip := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const he
  filter_upwards [hE, hb, hbad, hrecip, eventually_gt_atTop 1] with N hEN hbN hbadN hrecipN hN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hprod : (Nat.primeCounting (N/K) : ℝ) * energy N / (N:ℝ)^2 < (ε/3)^2 := by
    calc
      _ ≤ (Nat.primeCounting (N/K) : ℝ) * (C*N*Real.log N) / (N:ℝ)^2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEN (Nat.cast_nonneg _)) (sq_nonneg _)
      _ = C * ((Nat.primeCounting (N/K) : ℝ) * Real.log N / N) := by field_simp
      _ ≤ C * (2 * (Real.log 4+1) / K) := mul_le_mul_of_nonneg_left hbN hC.le
      _ = 2 * (Real.log 4+1) * C / K := by ring
      _ < (ε/3)^2 := hsmall
  have hl : Real.sqrt (Nat.primeCounting (N/K) * energy N) / N < ε/3 := by
    rw [← Real.sqrt_sq hn.le, ← Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg N))]
    exact (Real.sqrt_lt (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (energy_nonneg N))
      (sq_nonneg _)) he.le).mpr hprod
  have hh := div_le_div_of_nonneg_right (total_abs_cropped_bound hK (by omega : 0 < N)) hn.le
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn]
  simp only [add_div] at hh
  linarith

end Erdos371CroppedEnergy

#print axioms Erdos371CroppedEnergy.total_abs_cropped_bound

#print axioms Erdos371CroppedEnergy.density_half_of_eventually_n_log_energy
