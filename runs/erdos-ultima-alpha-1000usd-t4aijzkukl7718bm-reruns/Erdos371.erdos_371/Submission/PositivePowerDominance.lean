import FormalConjecturesUtil
import Submission.PowerWeightBoundary

/-! Largest-term domination for each fixed positive real power of distinct
prime divisors. This is an unsigned estimate, not a proof of Erdős 371.
The exponent is fixed before taking the counting limit. -/

namespace Erdos371PositivePowerDominance

open Finset Filter Erdos371PrimeDiscrepancy Erdos371PrimeHarmonicBlocks
open Erdos371SmallPrimeAveraging Erdos371ReflectionRange
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def tail (s : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ n.primeFactors, if q<P n then ((q:ℝ)/(P n:ℝ))^s else 0

noncomputable def bigTail (s : ℝ) (K n : ℕ) : ℝ :=
  ∑ q ∈ n.primeFactors.filter (fun q => 2^K≤q),
    if q<P n then ((q:ℝ)/(P n:ℝ))^s else 0

noncomputable def coeff (s : ℝ) (d : ℕ) : ℝ := (2*(1/(2:ℝ))^d)^s

noncomputable def constant (s : ℝ) : ℝ := 32*(2:ℝ)^s/(1-(1/(2:ℝ))^s)

noncomputable def pairMajorant (s : ℝ) (K T n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
    coeff s d * ∑ q ∈ block k, ∑ p ∈ block (k+d), ind (p*q) n

lemma coeff_nonneg (s : ℝ) (d : ℕ) : 0 ≤ coeff s d := by
  unfold coeff
  positivity

lemma coeff_eq (s : ℝ) (d : ℕ) :
    coeff s d = (2:ℝ)^s * ((1/(2:ℝ))^s)^d := by
  unfold coeff
  rw [Real.mul_rpow (by norm_num) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num), mul_comm (d:ℝ) s,
    Real.rpow_mul_natCast (by norm_num)]

lemma coeff_sum_bound {s : ℝ} (hs : 0<s) (T : ℕ) :
    (∑ d ∈ range T, coeff s d) ≤ (2:ℝ)^s/(1-(1/(2:ℝ))^s) := by
  have hr : (1/(2:ℝ))^s < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
  have hr0 : 0 ≤ (1/(2:ℝ))^s := by positivity
  simp_rw [coeff_eq]
  rw [← mul_sum]
  have hh := (summable_geometric_of_lt_one hr0 hr).sum_le_tsum
    (range T) (fun _ _ => by positivity)
  rw [tsum_geometric_of_lt_one hr0 hr] at hh
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hh
    (show (0:ℝ) ≤ (2:ℝ)^s by positivity)

lemma tail_nonneg (s : ℝ) (n : ℕ) : 0 ≤ tail s n := by
  unfold tail
  exact sum_nonneg fun _ _ => by split_ifs <;> positivity

lemma bigTail_nonneg (s : ℝ) (K n : ℕ) : 0 ≤ bigTail s K n := by
  unfold bigTail
  exact sum_nonneg fun _ _ => by split_ifs <;> positivity

lemma mean_pairMajorant_bound {s : ℝ} (hs : 0<s) {K : ℕ} (hK : 0<K) (T N : ℕ) :
    mean (pairMajorant s K T) N ≤ constant s/(K:ℝ) := by
  have he : mean (pairMajorant s K T) N =
      ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
        coeff s d * ∑ q ∈ block k, ∑ p ∈ block (k+d), mean (ind (p*q)) N := by
    change mean (fun n => pairMajorant s K T n) N = _
    simp only [pairMajorant, mean_sum, mean_const_mul]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
        coeff s d * pairMass k (k+d) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (coeff_nonneg s d)
      unfold pairMass
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro p hp
      simpa [Nat.cast_mul,mul_comm] using Erdos371AdditivePrimeDominance.mean_ind_le (p*q) N
    _ = ∑ d ∈ Finset.range T,
        coeff s d * ∑ k ∈ Finset.Ico K T, pairMass k (k+d) := by
      rw [Finset.sum_comm]
      simp [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.range T, coeff s d * (32/(K:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (Erdos371AdditivePrimeDominance.offset_mass_bound hK d T) (coeff_nonneg s d)
    _ = (32/(K:ℝ)) * ∑ d ∈ Finset.range T, coeff s d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (32/(K:ℝ))*((2:ℝ)^s/(1-(1/(2:ℝ))^s)) :=
      mul_le_mul_of_nonneg_left (coeff_sum_bound hs T) (by positivity)
    _ = _ := by unfold constant; ring

lemma block_power_ratio_bound {s : ℝ} (hs : 0<s) {q p k d : ℕ}
    (hq : q∈block k) (hp : p∈block (k+d)) :
    ((q:ℝ)/(p:ℝ))^s ≤ coeff s d := by
  exact Real.rpow_le_rpow (by positivity)
    (Erdos371AdditivePrimeDominance.block_ratio_bound hq hp) hs.le

lemma one_term_majorized {s : ℝ} (hs : 0<s) {n N k q : ℕ} (hn : n<N) (hq : q∈block k) :
    (if q∣n+1 ∧ q<P (n+1) then ((q:ℝ)/(P (n+1):ℝ))^s else 0) ≤
      ∑ d ∈ Finset.range (N+1), coeff s d *
        ∑ p ∈ block (k+d), ind (p*q) n := by
  by_cases hh : q∣n+1 ∧ q<P (n+1)
  · rw [if_pos hh]
    let p := P (n+1)
    let j := Nat.log 2 p
    have hp : p.Prime := Nat.prime_maxPrimeFac_of_one_lt (n+1) (by
      have := (mem_block.mp hq).1.two_le
      have hb : P (n+1)≤n+1 := Nat.maxPrimeFac_le
      omega)
    have hpj : p∈block j := Erdos371ComparableLowProduct.block_of_log hp
    have hkj : k≤j := by
      apply Nat.le_log_of_pow_le (by decide)
      exact (mem_block.mp hq).2.1.trans hh.2.le
    have hjN : j<N+1 := by
      have hlog := Nat.log_le_self 2 p
      have hpN : p≤N := Nat.maxPrimeFac_le.trans (by omega)
      dsimp only [j]
      omega
    have he : k+(j-k)=j := by omega
    have hmem : j-k∈Finset.range (N+1) := Finset.mem_range.mpr (by omega)
    have hprod : p*q∣n+1 := by
      apply ((Nat.coprime_primes hp (mem_block.mp hq).1).mpr (by omega)).mul_dvd_of_dvd_of_dvd
      · exact Nat.maxPrimeFac_dvd
      · exact hh.1
    calc
      _ ≤ coeff s (j-k) := block_power_ratio_bound hs hq (by simpa only [he] using hpj)
      _ = coeff s (j-k) * ind (p*q) n := by simp [ind,hprod]
      _ ≤ coeff s (j-k) * ∑ p' ∈ block (k+(j-k)), ind (p'*q) n := by
        apply mul_le_mul_of_nonneg_left _ (by simp only [coeff]; positivity)
        apply Finset.single_le_sum (f := fun p' => ind (p'*q) n)
          (fun _ _ => by simp only [ind]; positivity)
        simpa only [he] using hpj
      _ ≤ _ := Finset.single_le_sum
        (f := fun d => coeff s d * ∑ p ∈ block (k+d), ind (p*q) n)
        (fun _ _ => by simp only [ind, coeff]; positivity) hmem
  · rw [if_neg hh]
    unfold ind coeff
    positivity

lemma bigTail_le_majorant {s : ℝ} (hs : 0<s) {n N : ℕ} (hn : n<N) (K : ℕ) :
    bigTail s K (n+1) ≤ pairMajorant s K (N+1) n := by
  let fs := (n+1).primeFactors.filter (fun q => 2^K≤q)
  have hmap : ∀ q∈fs, Nat.log 2 q∈Finset.Ico K (N+1) := by
    intro q hq
    obtain ⟨hq,hKq⟩ := Finset.mem_filter.mp hq
    have hpq := Nat.mem_primeFactors.mp hq
    have hqN : q≤N := (Nat.le_of_dvd (by omega : 0<n+1) hpq.2.1).trans (by omega)
    exact Finset.mem_Ico.mpr ⟨Nat.le_log_of_pow_le (by decide) hKq,
      (Nat.log_le_self 2 q).trans_lt (by omega)⟩
  unfold bigTail
  change (∑ q∈fs, if q<P (n+1) then ((q:ℝ)/(P (n+1):ℝ))^s else 0) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  unfold pairMajorant
  apply Finset.sum_le_sum
  intro k hk
  have hsub : fs.filter (fun q => Nat.log 2 q=k) ⊆ block k := by
    intro q hq
    obtain ⟨hqs,hlog⟩ := Finset.mem_filter.mp hq
    have hpq := Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqs).1
    simpa only [hlog] using Erdos371ComparableLowProduct.block_of_log hpq.1
  have he : (∑ q ∈ fs.filter (fun q => Nat.log 2 q=k),
      if q<P (n+1) then ((q:ℝ)/(P (n+1):ℝ))^s else 0) =
      ∑ q ∈ fs.filter (fun q => Nat.log 2 q=k),
      if q∣n+1 ∧ q<P (n+1) then ((q:ℝ)/(P (n+1):ℝ))^s else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    have hd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.1
    simp [hd]
  rw [he]
  calc
    _ ≤ ∑ q ∈ block k, if q∣n+1 ∧ q<P (n+1) then ((q:ℝ)/(P (n+1):ℝ))^s else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by split_ifs <;> positivity)
    _ ≤ ∑ q ∈ block k, ∑ d ∈ Finset.range (N+1), coeff s d *
        ∑ p ∈ block (k+d), ind (p*q) n :=
      Finset.sum_le_sum (fun q hq => one_term_majorized hs hn hq)
    _ = _ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]

lemma mean_bigTail_bound {s : ℝ} (hs : 0<s) {K : ℕ} (hK : 0<K) (N : ℕ) :
    mean (fun n => bigTail s K (n+1)) N ≤ constant s/(K:ℝ) := by
  apply le_trans _ (mean_pairMajorant_bound hs hK (N+1) N)
  unfold mean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact Finset.sum_le_sum (fun n hn => bigTail_le_majorant hs (Finset.mem_range.mp hn) K)


lemma inverse_power_mean_tendsto_zero {s : ℝ} (hs : 0<s) :
    Tendsto (mean (fun n => (1/(P (n+1):ℝ))^s)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hy := tendsto_one_div_atTop_nhds_zero_nat.rpow_const (Or.inr hs.le)
  simp only [Real.zero_rpow hs.ne'] at hy
  obtain ⟨Y,hY,hsmall⟩ := ((eventually_gt_atTop 0).and
    (hy.eventually_lt_const (half_pos hε))).exists
  have hd := Erdos371CofactorDensity.density_zero_shift
    (Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero Y)
  filter_upwards [hd.eventually_lt_const (half_pos hε), eventually_gt_atTop 0]
    with N hSN hN
  have hbound : mean (fun n => (1/(P (n+1):ℝ))^s) N ≤
      {n | P (n+1)≤Y}.partialDensity Set.univ N + (1/(Y:ℝ))^s := by
    rw [← indicator_mean_eq_density,← mean_const ((1/(Y:ℝ))^s) hN,← mean_add]
    apply mean_mono
    intro n
    have hp : (1:ℝ)≤P (n+1) := by
      exact_mod_cast Erdos371AdditivePrimeDominance.maxPrimeFac_succ_pos n
    by_cases h : P (n+1)≤Y
    · simp only [Set.mem_setOf_eq,h,if_true]
      have hh : 1/(P (n+1):ℝ)≤1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
      have hh' := Real.rpow_le_rpow (by positivity) hh hs.le
      rw [Real.one_rpow] at hh'
      exact hh'.trans (le_add_of_nonneg_right (by positivity))
    · simp only [Set.mem_setOf_eq,h,if_false,zero_add]
      apply Real.rpow_le_rpow (by positivity) _ hs.le
      exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hY)
        (by exact_mod_cast (by omega : Y≤P (n+1)))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mean_nonneg (fun _ => by positivity) N)]
  change {n | P (n+1)≤Y}.partialDensity Set.univ N < ε/2 at hSN
  change (1/(Y:ℝ))^s<ε/2 at hsmall
  linarith

noncomputable def smallWeight (s : ℝ) (K : ℕ) : ℝ :=
  ∑ q ∈ range (2^K), (q:ℝ)^s

lemma tail_small_big (s : ℝ) (K n : ℕ) :
    tail s n ≤ smallWeight s K * (1/(P n:ℝ))^s + bigTail s K n := by
  let fs := n.primeFactors.filter (fun q => ¬2^K≤q)
  let f : ℕ → ℝ := fun q => if q<P n then ((q:ℝ)/(P n:ℝ))^s else 0
  have he : tail s n = (∑ q∈fs, f q)+bigTail s K n := by
    have hh := Finset.sum_filter_add_sum_filter_not n.primeFactors
      (fun q => 2^K≤q) f
    simpa only [tail,bigTail,fs,f,add_comm] using hh.symm
  rw [he]
  apply add_le_add _ le_rfl
  have hsub : fs ⊆ Finset.range (2^K) := by
    intro q hq
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hq).2; omega)
  calc
    _ ≤ ∑ q∈fs, ((q:ℝ)/(P n:ℝ))^s := Finset.sum_le_sum (fun q hq => by
      dsimp [f]; split_ifs <;> first | exact le_rfl | positivity)
    _ ≤ ∑ q∈Finset.range (2^K), ((q:ℝ)/(P n:ℝ))^s :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = _ := by
      unfold smallWeight
      rw [sum_mul]
      apply sum_congr rfl
      intro q hq
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
      simp only [one_div]

lemma tail_shift_mean_bound {s : ℝ} (hs : 0<s) {K : ℕ} (hK : 0<K) (N : ℕ) :
    mean (fun n => tail s (n+1)) N ≤
      smallWeight s K * mean (fun n => (1/(P (n+1):ℝ))^s) N + constant s/(K:ℝ) := by
  have hh := mean_mono (fun n => tail_small_big s K (n+1)) N
  rw [mean_add, mean_const_mul] at hh
  exact hh.trans (add_le_add le_rfl (mean_bigTail_bound hs hK N))

/-- Every positive exponent is fixed before taking the counting limit.
There is no assertion of uniform convergence as the exponent tends to zero. -/
theorem tail_shift_mean_tendsto_zero {s : ℝ} (hs : 0<s) :
    Tendsto (mean (fun n => tail s (n+1))) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K,hK,hsmall⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat (constant s)).eventually_lt_const
      (half_pos hε))).exists
  have hd := (inverse_power_mean_tendsto_zero hs).const_mul (smallWeight s K)
  simp only [mul_zero] at hd
  filter_upwards [hd.eventually_lt_const (half_pos hε)] with N hN
  rw [Real.dist_eq,sub_zero,
    abs_of_nonneg (mean_nonneg (fun n => tail_nonneg s (n+1)) N)]
  change constant s/(K:ℝ)<ε/2 at hsmall
  linarith [tail_shift_mean_bound hs hK N]

lemma tail_zero (s : ℝ) : tail s 0=0 := by simp [tail]

theorem tail_mean_tendsto_zero {s : ℝ} (hs : 0<s) :
    Tendsto (mean (tail s)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tail_shift_mean_tendsto_zero hs)
  · exact fun N => mean_nonneg (tail_nonneg s) N
  · intro N
    unfold mean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hh := Finset.sum_range_succ' (tail s) N
    rw [Finset.sum_range_succ,tail_zero] at hh
    linarith [tail_nonneg s N]

lemma tail_eq_powerTail (s : ℝ) (n : ℕ) :
    tail s n = Erdos371PowerWeightBoundary.powerTail s n := by
  simp only [tail, Erdos371PowerWeightBoundary.powerTail,
    Erdos371PowerWeightBoundary.properPrimes, sum_filter]

theorem powerTail_mean_tendsto_zero {s : ℝ} (hs : 0<s) :
    Tendsto (mean (Erdos371PowerWeightBoundary.powerTail s)) atTop (𝓝 0) := by
  have he : tail s = Erdos371PowerWeightBoundary.powerTail s :=
    funext (tail_eq_powerTail s)
  rw [← he]
  exact tail_mean_tendsto_zero hs

theorem powerTail_shift_mean_tendsto_zero {s : ℝ} (hs : 0<s) :
    Tendsto (mean (fun n => Erdos371PowerWeightBoundary.powerTail s (n+1)))
      atTop (𝓝 0) := by
  simpa only [tail_eq_powerTail] using tail_shift_mean_tendsto_zero hs

lemma tail_antitone (n : ℕ) : Antitone (fun s : ℝ => tail s n) := by
  intro s t hst
  unfold tail
  apply sum_le_sum
  intro q hq
  by_cases h : q<P n
  · simp only [if_pos h]
    have hqpos : (0:ℝ)<q := Nat.cast_pos.mpr (Nat.mem_primeFactors.mp hq).1.pos
    have hqP : (q:ℝ)<P n := Nat.cast_lt.mpr h
    have hPpos : (0:ℝ)<P n := hqpos.trans hqP
    exact Real.rpow_le_rpow_of_exponent_ge (div_pos hqpos hPpos)
      ((div_le_one hPpos).mpr hqP.le) hst
  · simp only [if_neg h, le_refl]

/-- Uniformity is available when the moving exponents stay bounded away from
zero. No conclusion is asserted for exponents tending to zero. -/
theorem moving_powerTail_mean_tendsto_zero (exponent : ℕ → ℝ)
    {δ : ℝ} (hδ : 0<δ) (h : ∀ᶠ N in atTop, δ ≤ exponent N) :
    Tendsto (fun N => mean (Erdos371PowerWeightBoundary.powerTail (exponent N)) N)
      atTop (𝓝 0) := by
  have hnonneg (N : ℕ) : 0 ≤ mean (tail (exponent N)) N :=
    mean_nonneg (tail_nonneg _) N
  have hbound : ∀ᶠ N in atTop, mean (tail (exponent N)) N ≤ mean (tail δ) N := by
    filter_upwards [h] with N hN
    exact mean_mono (fun n => tail_antitone n hN) N
  have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tail_mean_tendsto_zero hδ) (Eventually.of_forall hnonneg) hbound
  have he (s : ℝ) : tail s = Erdos371PowerWeightBoundary.powerTail s :=
    funext (tail_eq_powerTail s)
  simpa only [he] using ht

end Erdos371PositivePowerDominance

#print axioms Erdos371PositivePowerDominance.powerTail_mean_tendsto_zero
#print axioms Erdos371PositivePowerDominance.powerTail_shift_mean_tendsto_zero

#print axioms Erdos371PositivePowerDominance.moving_powerTail_mean_tendsto_zero
