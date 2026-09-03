import FormalConjecturesUtil
import Submission.ElementaryEnergy
import Submission.LogSmoothCount

/-! A prime-weighted energy criterion for the comparison discrepancy.
The unconditional bound proved here is quadratic. A little-o improvement is
an explicit hypothesis, not an unconditional result. -/

namespace Erdos371WeightedPrimeEnergy

open Erdos371PrimeDiscrepancy Erdos371ElementaryEnergy Filter
open scoped Topology

def weightedEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, (p:ℝ) * (group p N:ℝ)^2

def absoluteTotal (N : ℕ) : ℝ :=
  ∑ p ∈ (N+1).primesBelow, |(group p N:ℝ)|

lemma weightedEnergy_nonneg (N : ℕ) : 0 ≤ weightedEnergy N := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

lemma absoluteTotal_nonneg (N : ℕ) : 0 ≤ absoluteTotal N :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma absoluteTotal_le (N : ℕ) : absoluteTotal N ≤ N := sum_group_abs_le _ N

lemma weightedEnergy_le_mul_absoluteTotal (N : ℕ) :
    weightedEnergy N ≤ N * absoluteTotal N := by
  unfold weightedEnergy absoluteTotal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := Nat.prime_of_mem_primesBelow hp
  have hdiv : |(group p N:ℝ)| ≤ (N:ℝ)/p :=
    (group_abs_le_div hprime N).trans Nat.cast_div_le
  have hmul := (le_div_iff₀ (Nat.cast_pos.mpr hprime.pos)).mp hdiv
  have hh := mul_le_mul_of_nonneg_right hmul (abs_nonneg (group p N:ℝ))
  nlinarith [sq_abs (group p N:ℝ)]

lemma weightedEnergy_le_sq (N : ℕ) : weightedEnergy N ≤ (N:ℝ)^2 := by
  have h := mul_le_mul_of_nonneg_left (absoluteTotal_le N) (Nat.cast_nonneg (α := ℝ) N)
  nlinarith [weightedEnergy_le_mul_absoluteTotal N]

lemma low_absoluteTotal_le (K N : ℕ) :
    (∑ p ∈ (N+1).primesBelow with p ≤ K, |(group p N:ℝ)|) ≤
      (((Finset.range N).filter fun n => P n ≤ K).card:ℝ) := by
  let s := (N+1).primesBelow.filter fun p => p ≤ K
  calc
    _ ≤ ∑ p ∈ s, (((Finset.range N).filter fun n => winner n = p).card:ℝ) :=
      Finset.sum_le_sum (fun p _ => group_abs_le_count p N)
    _ = ∑ n ∈ Finset.range N, (if winner n ∈ s then (1:ℝ) else 0) := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm]
      simp
    _ ≤ ∑ n ∈ Finset.range N, (if P n ≤ K then (1:ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hw : winner n ∈ s
      · have hle := (Finset.mem_filter.mp hw).2
        have hpn : P n ≤ K := (le_max_left _ _).trans hle
        simp [hw, hpn]
      · simp only [hw, if_false]
        split_ifs <;> norm_num
    _ = _ := by simp

lemma high_reciprocal_bound {K N : ℕ} (hK : 1 < K) (hN : 0 < N) :
    (∑ p ∈ (N+1).primesBelow with K < p, 1/(p:ℝ)) ≤
      (Real.log N + Real.log 4)/Real.log K := by
  have hlog : 0 < Real.log (K:ℝ) := Real.log_pos (by exact_mod_cast hK)
  apply (le_div_iff₀ hlog).mpr
  calc
    _ = ∑ p ∈ (N+1).primesBelow with K < p, Real.log (K:ℝ)/(p:ℝ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ (N+1).primesBelow with K < p, Real.log (p:ℝ)/(p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hkp := (Finset.mem_filter.mp hp).2
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
      exact Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < K)) (by exact_mod_cast hkp.le)
    _ ≤ ∑ p ∈ (N+1).primesBelow, Real.log (p:ℝ)/(p:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ ≤ _ := Erdos371LogSmoothCount.prime_log_div_bound hN

lemma high_absoluteTotal_sq_le (K N : ℕ) :
    (∑ p ∈ (N+1).primesBelow with K < p, |(group p N:ℝ)|)^2 ≤
      (∑ p ∈ (N+1).primesBelow with K < p, 1/(p:ℝ)) * weightedEnergy N := by
  let s := (N+1).primesBelow.filter fun p => K < p
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
    (r := fun p => |(group p N:ℝ)|) (f := fun p => 1/(p:ℝ))
    (g := fun p => (p:ℝ)*(group p N:ℝ)^2)
    (fun p _ => by positivity) (fun p _ => by positivity)
    (fun p hp => by
      have hp0 : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
        (Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1).ne_zero
      rw [sq_abs]
      field_simp)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun p _ => by positivity))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun p _ _ => by positivity)

lemma absoluteTotal_cutoff_bound {K N : ℕ} (hK : 1 < K) (hN : 1 < N) :
    absoluteTotal N ≤ Real.sqrt N + 1 +
      4*N*(Real.log K + Real.log 4)/Real.log N +
      Real.sqrt (((Real.log N + Real.log 4)/Real.log K) * weightedEnergy N) := by
  have hc : (∑ p ∈ (N+1).primesBelow with K < p, |(group p N:ℝ)|) ≤
      Real.sqrt (((Real.log N + Real.log 4)/Real.log K) * weightedEnergy N) := by
    apply Real.le_sqrt_of_sq_le
    exact (high_absoluteTotal_sq_le K N).trans
      (mul_le_mul_of_nonneg_right (high_reciprocal_bound hK (by omega)) (weightedEnergy_nonneg N))
  have he := Finset.sum_filter_add_sum_filter_not (N+1).primesBelow
    (fun p => p ≤ K) (fun p => |(group p N:ℝ)|)
  simp only [not_le] at he
  have hl := low_absoluteTotal_le K N
  have hncard : (((Finset.range N).filter fun n => P n ≤ K).card:ℝ) ≤
      (((Finset.range (N+1)).filter fun n => P n ≤ K).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter
      (fun n => P n ≤ K) (Finset.range_mono (by omega : N ≤ N+1)))
  have hs := Erdos371LogSmoothCount.smooth_count_log_bound (by omega : 0 < K) hN
  unfold absoluteTotal
  linarith

noncomputable def powerCutoff (δ : ℝ) (N : ℕ) : ℕ := ⌈(N:ℝ)^δ⌉₊

lemma powerCutoff_bounds {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 1 < N) :
    1 < powerCutoff δ N ∧
    δ * Real.log (N:ℝ) ≤ Real.log (powerCutoff δ N : ℝ) ∧
    Real.log (powerCutoff δ N : ℝ) ≤ Real.log 2 + δ * Real.log (N:ℝ) := by
  have hn : (1:ℝ) < N := by exact_mod_cast hN
  have hp : 1 < (N:ℝ)^δ := Real.one_lt_rpow hn hδ
  have hc : (N:ℝ)^δ ≤ (powerCutoff δ N:ℝ) := Nat.le_ceil _
  have hk : 1 < powerCutoff δ N := by exact_mod_cast hp.trans_le hc
  refine ⟨hk, ?_, ?_⟩
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) δ) hc
    simpa [Real.log_rpow (by linarith : (0:ℝ) < N)] using hh
  · have hceil : (powerCutoff δ N:ℝ) < (N:ℝ)^δ + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    have hle : (powerCutoff δ N:ℝ) ≤ 2*(N:ℝ)^δ := by linarith
    have hh := Real.log_le_log (Nat.cast_pos.mpr (by omega : 0 < powerCutoff δ N)) hle
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (by linarith) δ).ne',
      Real.log_rpow (by linarith : (0:ℝ) < N)] at hh
    exact hh

lemma normalized_cutoff_bound {K N : ℕ} (hK : 1 < K) (hN : 1 < N) :
    absoluteTotal N / N ≤ (Real.sqrt N+1)/N +
      4*(Real.log K+Real.log 4)/Real.log N +
      Real.sqrt (((Real.log N+Real.log 4)/Real.log K) *
        (weightedEnergy N/(N:ℝ)^2)) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hh := div_le_div_of_nonneg_right (absoluteTotal_cutoff_bound hK hN) hn.le
  have hs : Real.sqrt (((Real.log N+Real.log 4)/Real.log K) * weightedEnergy N) / N =
      Real.sqrt (((Real.log N+Real.log 4)/Real.log K) *
        (weightedEnergy N/(N:ℝ)^2)) := by
    rw [← mul_div_assoc, Real.sqrt_div (mul_nonneg
      (div_nonneg (add_nonneg (Real.log_natCast_nonneg N) (by positivity))
        (Real.log_natCast_nonneg K)) (weightedEnergy_nonneg N)), Real.sqrt_sq hn.le]
  calc
    _ ≤ _ := hh
    _ = _ := by rw [add_div, add_div, hs]; field_simp

lemma normalized_power_cutoff_bound {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 4 ≤ N) :
    absoluteTotal N / N ≤ (Real.sqrt N+1)/N + 4*δ +
      4*(Real.log 2+Real.log 4)/Real.log N +
      Real.sqrt ((2/δ)*(weightedEnergy N/(N:ℝ)^2)) := by
  obtain ⟨hK, hlo, hhi⟩ := powerCutoff_bounds hδ (by omega : 1 < N)
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogK : 0 < Real.log (powerCutoff δ N:ℝ) := Real.log_pos (by exact_mod_cast hK)
  have h4 : Real.log 4 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hr : (Real.log (N:ℝ)+Real.log 4)/Real.log (powerCutoff δ N:ℝ) ≤ 2/δ := by
    apply (div_le_div_iff₀ hlogK hδ).mpr
    nlinarith
  have hlow : 4*(Real.log (powerCutoff δ N:ℝ)+Real.log 4)/Real.log (N:ℝ) ≤
      4*δ + 4*(Real.log 2+Real.log 4)/Real.log (N:ℝ) := by
    apply (div_le_iff₀ hlog).mpr
    have he : (4*δ + 4*(Real.log 2+Real.log 4)/Real.log (N:ℝ))*Real.log (N:ℝ) =
        4*δ*Real.log (N:ℝ) + 4*(Real.log 2+Real.log 4) := by field_simp
    rw [he]
    linarith
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hr
    (div_nonneg (weightedEnergy_nonneg N) (sq_nonneg (N:ℝ))))
  have hh := normalized_cutoff_bound hK (by omega : 1 < N)
  linarith

lemma cutoff_error_tendsto_zero :
    Tendsto (fun N : ℕ => (Real.sqrt N+1)/N +
      4*(Real.log 2+Real.log 4)/Real.log N) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt N/(N:ℝ)) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => 4*(Real.log 2+Real.log 4)/Real.log N) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hl)
  simpa [add_div] using (hs.add tendsto_one_div_atTop_nhds_zero_nat).add hc

lemma absoluteTotal_mean_tendsto_zero_of_weightedEnergy
    (hW : Tendsto (fun N : ℕ => weightedEnergy N/(N:ℝ)^2) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => absoluteTotal N/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hs : Tendsto (fun N : ℕ => Real.sqrt ((2/δ)*(weightedEnergy N/(N:ℝ)^2)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hW).sqrt
  have ht := cutoff_error_tendsto_zero.add hs
  simp only [add_zero] at ht
  have he := ht.eventually_lt_const (half_pos hε)
  filter_upwards [he, eventually_ge_atTop 4] with N hsmall hN
  have hb := normalized_power_cutoff_bound hδ hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (div_nonneg (absoluteTotal_nonneg N) (Nat.cast_nonneg N))]
  dsimp [δ] at hb hsmall
  linarith

lemma weightedEnergy_tendsto_zero_of_absoluteTotal
    (hA : Tendsto (fun N : ℕ => absoluteTotal N/N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => weightedEnergy N/(N:ℝ)^2) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hA
  · exact Eventually.of_forall fun N => div_nonneg (weightedEnergy_nonneg N) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    calc
      _ ≤ ((N:ℝ)*absoluteTotal N)/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right (weightedEnergy_le_mul_absoluteTotal N) (sq_nonneg _)
      _ = _ := by field_simp

/-- Prime-weighted subquadratic energy is equivalent to average absolute
cancellation of the individual winning-prime groups. Neither condition is
asserted to hold unconditionally. -/
theorem weightedEnergy_iff_absoluteTotal :
    Tendsto (fun N : ℕ => weightedEnergy N/(N:ℝ)^2) atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => absoluteTotal N/N) atTop (𝓝 0) :=
  ⟨absoluteTotal_mean_tendsto_zero_of_weightedEnergy,
    weightedEnergy_tendsto_zero_of_absoluteTotal⟩

lemma density_half_of_absoluteTotal
    (hA : Tendsto (fun N : ℕ => absoluteTotal N/N) atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) := by
  apply density_half_iff_prime_discrepancy.mpr
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA
  · intro N
    exact abs_nonneg _
  · intro N
    change |((∑ p ∈ (N+1).primesBelow, group p N : ℤ):ℝ) / N| ≤ absoluteTotal N/N
    rw [abs_div, show |(N:ℝ)| = (N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    push_cast
    exact Finset.abs_sum_le_sum_abs _ _

/-- A little-o improvement on the unconditional bound `weightedEnergy N ≤ N²`
would settle the density conjecture. The little-o estimate remains a hypothesis. -/
theorem density_half_of_weightedEnergy_subquadratic
    (hW : Tendsto (fun N : ℕ => weightedEnergy N/(N:ℝ)^2) atTop (𝓝 0)) :
    {n | P n < P (n+1)}.HasDensity (1/2) :=
  density_half_of_absoluteTotal (absoluteTotal_mean_tendsto_zero_of_weightedEnergy hW)

end Erdos371WeightedPrimeEnergy

#print axioms Erdos371WeightedPrimeEnergy.weightedEnergy_le_sq
#print axioms Erdos371WeightedPrimeEnergy.weightedEnergy_iff_absoluteTotal
#print axioms Erdos371WeightedPrimeEnergy.density_half_of_weightedEnergy_subquadratic
