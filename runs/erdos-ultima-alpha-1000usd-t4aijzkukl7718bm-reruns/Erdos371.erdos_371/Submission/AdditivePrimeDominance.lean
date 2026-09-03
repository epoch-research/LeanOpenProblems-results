import FormalConjecturesUtil
import Submission.CofactorPrimeGap

/-! First-moment domination of the sum of distinct prime factors by its
largest term. These estimates do not assert cancellation of adjacent signs. -/

namespace Erdos371AdditivePrimeDominance

open Finset Filter Erdos371PrimeDiscrepancy Erdos371PrimeHarmonicBlocks
open Erdos371SmallPrimeAveraging Erdos371ReflectionRange
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def tailRatio (n : ℕ) : ℝ :=
  ∑ q ∈ n.primeFactors, if q<P n then (q:ℝ)/(P n:ℝ) else 0

noncomputable def bigTail (K n : ℕ) : ℝ :=
  ∑ q ∈ n.primeFactors.filter (fun q => 2^K≤q),
    if q<P n then (q:ℝ)/(P n:ℝ) else 0

noncomputable def pairMajorant (K T n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
    2*(1/(2:ℝ))^d * ∑ q ∈ block k, ∑ p ∈ block (k+d), ind (p*q) n

lemma tailRatio_nonneg (n : ℕ) : 0≤tailRatio n := by
  unfold tailRatio
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma bigTail_nonneg (K n : ℕ) : 0≤bigTail K n := by
  unfold bigTail
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma pairMajorant_nonneg (K T n : ℕ) : 0≤pairMajorant K T n := by
  unfold pairMajorant ind
  positivity

lemma mean_ind_le (d N : ℕ) : mean (ind d) N ≤ 1/(d:ℝ) := by
  by_cases hN : N=0
  · subst N; simp [mean]
  · have hn : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [mean_ind]
    calc
      _ ≤ ((N:ℝ)/d)/N := div_le_div_of_nonneg_right Nat.cast_div_le hn.le
      _ = _ := by field_simp

lemma offset_mass_bound {K : ℕ} (hK : 0<K) (d T : ℕ) :
    (∑ k ∈ Finset.Ico K T, pairMass k (k+d)) ≤ 32/(K:ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, 16/(k:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact pairMass_le (hK.trans_le (Finset.mem_Ico.mp hk).1) (by omega)
    _ = 16 * ∑ k ∈ Finset.Ico K T, 1/(k:ℝ)^2 := by simp [Finset.mul_sum,div_eq_mul_inv]
    _ ≤ 16 * (2/(K:ℝ)) := mul_le_mul_of_nonneg_left
      (Erdos371TerminalCompression.sum_reciprocal_sq hK T) (by norm_num)
    _ = _ := by ring

lemma mean_pairMajorant_bound {K : ℕ} (hK : 0<K) (T N : ℕ) :
    mean (pairMajorant K T) N ≤ 128/(K:ℝ) := by
  have he : mean (pairMajorant K T) N =
      ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
        2*(1/(2:ℝ))^d * ∑ q ∈ block k, ∑ p ∈ block (k+d), mean (ind (p*q)) N := by
    change mean (fun n => pairMajorant K T n) N = _
    simp only [pairMajorant, mean_sum, mean_const_mul]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, ∑ d ∈ Finset.range T,
        2*(1/(2:ℝ))^d * pairMass k (k+d) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold pairMass
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro p hp
      simpa [Nat.cast_mul,mul_comm] using mean_ind_le (p*q) N
    _ = ∑ d ∈ Finset.range T,
        2*(1/(2:ℝ))^d * ∑ k ∈ Finset.Ico K T, pairMass k (k+d) := by
      rw [Finset.sum_comm]
      simp [Finset.mul_sum]
    _ ≤ ∑ d ∈ Finset.range T, 2*(1/(2:ℝ))^d * (32/(K:ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (offset_mass_bound hK d T) (by positivity)
    _ = (64/(K:ℝ)) * ∑ d ∈ Finset.range T, (1/(2:ℝ))^d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (64/(K:ℝ))*2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le T) (by positivity)
    _ = _ := by ring

lemma block_ratio_bound {q p k d : ℕ} (hq : q∈block k) (hp : p∈block (k+d)) :
    (q:ℝ)/(p:ℝ) ≤ 2*(1/(2:ℝ))^d := by
  have hqlo := (mem_block.mp hq).2.2
  have hplo := (mem_block.mp hp).2.1
  have hpp : (0:ℝ)<p := Nat.cast_pos.mpr (mem_block.mp hp).1.pos
  have hqbound : (q:ℝ) ≤ (2:ℝ)^(k+1) := by exact_mod_cast hqlo.le
  have hpbound : (2:ℝ)^(k+d) ≤ p := by exact_mod_cast hplo
  calc
    _ ≤ (2:ℝ)^(k+1)/(2:ℝ)^(k+d) := div_le_div₀ (by positivity) hqbound (by positivity) hpbound
    _ = _ := by rw [pow_add,pow_succ,one_div_pow]; field_simp; ring

lemma one_term_majorized {n N k q : ℕ} (hn : n<N) (hq : q∈block k) :
    (if q∣n+1 ∧ q<P (n+1) then (q:ℝ)/(P (n+1):ℝ) else 0) ≤
      ∑ d ∈ Finset.range (N+1), 2*(1/(2:ℝ))^d *
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
      _ ≤ 2*(1/(2:ℝ))^(j-k) := block_ratio_bound hq (by simpa only [he] using hpj)
      _ = 2*(1/(2:ℝ))^(j-k) * ind (p*q) n := by simp [ind,hprod]
      _ ≤ 2*(1/(2:ℝ))^(j-k) * ∑ p' ∈ block (k+(j-k)), ind (p'*q) n := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.single_le_sum (f := fun p' => ind (p'*q) n)
          (fun _ _ => by unfold ind; positivity)
        simpa only [he] using hpj
      _ ≤ _ := Finset.single_le_sum
        (f := fun d => 2*(1/(2:ℝ))^d * ∑ p ∈ block (k+d), ind (p*q) n)
        (fun _ _ => by unfold ind; positivity) hmem
  · rw [if_neg hh]
    unfold ind
    positivity

lemma bigTail_le_majorant {n N : ℕ} (hn : n<N) (K : ℕ) :
    bigTail K (n+1) ≤ pairMajorant K (N+1) n := by
  let s := (n+1).primeFactors.filter (fun q => 2^K≤q)
  have hmap : ∀ q∈s, Nat.log 2 q∈Finset.Ico K (N+1) := by
    intro q hq
    obtain ⟨hq,hKq⟩ := Finset.mem_filter.mp hq
    have hpq := Nat.mem_primeFactors.mp hq
    have hqN : q≤N := (Nat.le_of_dvd (by omega : 0<n+1) hpq.2.1).trans (by omega)
    exact Finset.mem_Ico.mpr ⟨Nat.le_log_of_pow_le (by decide) hKq,
      (Nat.log_le_self 2 q).trans_lt (by omega)⟩
  unfold bigTail
  change (∑ q∈s, if q<P (n+1) then (q:ℝ)/(P (n+1):ℝ) else 0) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  unfold pairMajorant
  apply Finset.sum_le_sum
  intro k hk
  have hsub : s.filter (fun q => Nat.log 2 q=k) ⊆ block k := by
    intro q hq
    obtain ⟨hqs,hlog⟩ := Finset.mem_filter.mp hq
    have hpq := Nat.mem_primeFactors.mp (Finset.mem_filter.mp hqs).1
    simpa only [hlog] using Erdos371ComparableLowProduct.block_of_log hpq.1
  have he : (∑ q ∈ s.filter (fun q => Nat.log 2 q=k),
      if q<P (n+1) then (q:ℝ)/(P (n+1):ℝ) else 0) =
      ∑ q ∈ s.filter (fun q => Nat.log 2 q=k),
      if q∣n+1 ∧ q<P (n+1) then (q:ℝ)/(P (n+1):ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    have hd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2.1
    simp [hd]
  rw [he]
  calc
    _ ≤ ∑ q ∈ block k, if q∣n+1 ∧ q<P (n+1) then (q:ℝ)/(P (n+1):ℝ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by split_ifs <;> positivity)
    _ ≤ ∑ q ∈ block k, ∑ d ∈ Finset.range (N+1), 2*(1/(2:ℝ))^d *
        ∑ p ∈ block (k+d), ind (p*q) n :=
      Finset.sum_le_sum (fun q hq => one_term_majorized hn hq)
    _ = _ := by rw [Finset.sum_comm]; simp [Finset.mul_sum]

lemma mean_bigTail_bound {K : ℕ} (hK : 0<K) (N : ℕ) :
    mean (fun n => bigTail K (n+1)) N ≤ 128/(K:ℝ) := by
  apply le_trans _ (mean_pairMajorant_bound hK (N+1) N)
  unfold mean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact Finset.sum_le_sum (fun n hn => bigTail_le_majorant (Finset.mem_range.mp hn) K)

lemma maxPrimeFac_succ_pos (n : ℕ) : 0<P (n+1) := by
  cases n with
  | zero => simp [P]
  | succ n => exact (Nat.prime_maxPrimeFac_of_one_lt (n+1+1) (by omega)).pos

lemma inverse_mean_tendsto_zero :
    Tendsto (mean (fun n => 1/(P (n+1):ℝ))) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y,hY,hsmall⟩ := ((eventually_gt_atTop 0).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (half_pos hε))).exists
  have hs := Erdos371CofactorDensity.density_zero_shift
    (Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero Y)
  filter_upwards [hs.eventually_lt_const (half_pos hε), eventually_gt_atTop 0]
    with N hSN hN
  have hbound : mean (fun n => 1/(P (n+1):ℝ)) N ≤
      {n | P (n+1)≤Y}.partialDensity Set.univ N + 1/(Y:ℝ) := by
    rw [← indicator_mean_eq_density,← mean_const (1/(Y:ℝ)) hN,← mean_add]
    apply mean_mono
    intro n
    have hp : (1:ℝ)≤P (n+1) := by exact_mod_cast maxPrimeFac_succ_pos n
    by_cases h : P (n+1)≤Y
    · simp only [Set.mem_setOf_eq,h,if_true]
      have hh : 1/(P (n+1):ℝ)≤1 := by
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hp
      linarith [show (0:ℝ)≤1/(Y:ℝ) by positivity]
    · simp only [Set.mem_setOf_eq,h,if_false,zero_add]
      exact one_div_le_one_div_of_le (Nat.cast_pos.mpr hY) (by exact_mod_cast (by omega : Y≤P (n+1)))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mean_nonneg (fun _ => by positivity) N)]
  change {n | P (n+1)≤Y}.partialDensity Set.univ N < ε/2 at hSN
  change 1/(Y:ℝ)<ε/2 at hsmall
  linarith

lemma tailRatio_small_big (K n : ℕ) :
    tailRatio n ≤ ((2^K:ℕ):ℝ)^2/(P n:ℝ)+bigTail K n := by
  let s := n.primeFactors.filter (fun q => ¬2^K≤q)
  let f : ℕ → ℝ := fun q => if q<P n then (q:ℝ)/(P n:ℝ) else 0
  have he : tailRatio n = (∑ q∈s, f q)+bigTail K n := by
    have hh := Finset.sum_filter_add_sum_filter_not n.primeFactors
      (fun q => 2^K≤q) f
    simpa only [tailRatio,bigTail,s,f,add_comm] using hh.symm
  rw [he]
  apply add_le_add _ le_rfl
  have hsub : s ⊆ Finset.range (2^K) := by
    intro q hq
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hq).2; omega)
  calc
    _ ≤ ∑ q∈s, (q:ℝ)/(P n:ℝ) := Finset.sum_le_sum (fun q hq => by
      dsimp [f]; split_ifs <;> first | exact le_rfl | positivity)
    _ ≤ ∑ q∈Finset.range (2^K), (q:ℝ)/(P n:ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ _q∈Finset.range (2^K), ((2^K:ℕ):ℝ)/(P n:ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.mem_range.mp hq).le) (by positivity)
    _ = _ := by simp [pow_two,mul_div_assoc]

lemma tailRatio_shift_mean_bound {K : ℕ} (hK : 0<K) (N : ℕ) :
    mean (fun n => tailRatio (n+1)) N ≤
      ((2^K:ℕ):ℝ)^2 * mean (fun n => 1/(P (n+1):ℝ)) N + 128/(K:ℝ) := by
  have hh := mean_mono (fun n => tailRatio_small_big K (n+1)) N
  rw [mean_add] at hh
  have he : mean (fun n => ((2^K:ℕ):ℝ)^2/(P (n+1):ℝ)) N =
      ((2^K:ℕ):ℝ)^2 * mean (fun n => 1/(P (n+1):ℝ)) N := by
    simpa [div_eq_mul_inv] using mean_const_mul (((2^K:ℕ):ℝ)^2)
      (fun n => 1/(P (n+1):ℝ)) N
  rw [he] at hh
  linarith [mean_bigTail_bound hK N]

/-- The relative contribution of all distinct prime factors other than the
largest tends to zero in the first mean. This is an unsigned assertion. -/
theorem tailRatio_shift_mean_tendsto_zero :
    Tendsto (mean (fun n => tailRatio (n+1))) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K,hK,hsmall⟩ := ((eventually_gt_atTop 0).and
    ((tendsto_const_div_atTop_nhds_zero_nat (128:ℝ)).eventually_lt_const (half_pos hε))).exists
  have hs := (inverse_mean_tendsto_zero.const_mul (((2^K:ℕ):ℝ)^2))
  simp only [mul_zero] at hs
  filter_upwards [hs.eventually_lt_const (half_pos hε)] with N hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mean_nonneg (fun n => tailRatio_nonneg (n+1)) N)]
  change 128/(K:ℝ)<ε/2 at hsmall
  linarith [tailRatio_shift_mean_bound hK N]

lemma tailRatio_zero : tailRatio 0=0 := by simp [tailRatio]

theorem tailRatio_mean_tendsto_zero : Tendsto (mean tailRatio) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tailRatio_shift_mean_tendsto_zero
  · exact fun N => mean_nonneg tailRatio_nonneg N
  · intro N
    unfold mean
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hh := Finset.sum_range_succ' tailRatio N
    rw [Finset.sum_range_succ,tailRatio_zero] at hh
    linarith [tailRatio_nonneg N]

lemma tailRatio_exception_hasDensity_zero {ε : ℝ} (hε : 0<ε) :
    {n | ε<tailRatio n}.HasDensity 0 := by
  have hs := tailRatio_mean_tendsto_zero.div_const ε
  simp only [zero_div] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
  · intro N
    unfold Set.partialDensity
    positivity
  · intro N
    change {n | ε<tailRatio n}.partialDensity Set.univ N ≤ mean tailRatio N/ε
    rw [← indicator_mean_eq_density]
    have he : mean tailRatio N/ε = mean (fun n => tailRatio n/ε) N := by
      simp [mean,Finset.sum_div,div_div,mul_comm]
    rw [he]
    apply mean_mono
    intro n
    by_cases h : ε<tailRatio n
    · simp only [Set.mem_setOf_eq,h,if_true]
      exact (le_div_iff₀ hε).mpr (by linarith)
    · simp only [Set.mem_setOf_eq,h,if_false]
      exact div_nonneg (tailRatio_nonneg n) hε.le

/-- The strongly additive sum of distinct prime factors. -/
noncomputable def primeSum (n : ℕ) : ℝ := ∑ p ∈ n.primeFactors, (p:ℝ)

lemma primeSum_mul_of_coprime {a b : ℕ} (h : a.Coprime b) :
    primeSum (a*b)=primeSum a+primeSum b := by
  simp only [primeSum,h.primeFactors_mul,Finset.sum_union h.disjoint_primeFactors]

lemma primeSum_eq {n : ℕ} (hn : 1<n) :
    primeSum n=(P n:ℝ)*(1+tailRatio n) := by
  have hp := Nat.prime_maxPrimeFac_of_one_lt n hn
  have hp0 : (P n:ℝ)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmem : P n∈n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp,Nat.maxPrimeFac_dvd,by omega⟩
  have ht : (P n:ℝ)*tailRatio n =
      ∑ q ∈ n.primeFactors, if q<P n then (q:ℝ) else 0 := by
    unfold tailRatio
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqP : q<P n
    · simp only [if_pos hqP]
      field_simp
    · simp [hqP]
  have hs : primeSum n = (P n:ℝ) +
      ∑ q ∈ n.primeFactors, if q<P n then (q:ℝ) else 0 := by
    unfold primeSum
    have he (q : ℕ) (hq : q∈n.primeFactors) : (q:ℝ) =
        (if q=P n then (P n:ℝ) else 0)+(if q<P n then (q:ℝ) else 0) := by
      obtain ⟨hprime,hd,hn0⟩ := Nat.mem_primeFactors.mp hq
      have hle : q≤P n := Nat.le_maxPrimeFac hn0 hprime hd
      by_cases h : q=P n
      · simp [h]
      · simp [h,show q<P n by omega]
    rw [Finset.sum_congr rfl he,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',hmem,if_true]
  rw [hs,← ht]
  ring

lemma primeSum_lower {n : ℕ} (hn : 1<n) : (P n:ℝ)≤primeSum n := by
  rw [primeSum_eq hn]
  nlinarith [tailRatio_nonneg n,Nat.cast_nonneg (α := ℝ) (P n)]

lemma primeSum_upper {n : ℕ} (hn : 1<n) (ht : tailRatio n≤1) :
    primeSum n≤2*(P n:ℝ) := by
  rw [primeSum_eq hn]
  nlinarith [Nat.cast_nonneg (α := ℝ) (P n)]

def comparisonGood (n : ℕ) : Prop := 1<n ∧ tailRatio n≤1 ∧ tailRatio (n+1)≤1 ∧
  2*min (P n) (P (n+1))< max (P n) (P (n+1))

lemma comparisonGood_complement_hasDensity_zero : {n | ¬comparisonGood n}.HasDensity 0 := by
  let A : Set ℕ := {n | P n≤2}
  let B : Set ℕ := {n | 1<tailRatio n}
  let C : Set ℕ := {n | 1<tailRatio (n+1)}
  let D : Set ℕ := {n | max (P n) (P (n+1))≤2*min (P n) (P (n+1))}
  have hA : A.HasDensity 0 := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero 2
  have hB : B.HasDensity 0 := tailRatio_exception_hasDensity_zero (by norm_num)
  have hC : C.HasDensity 0 := by
    change {n | n+1∈B}.HasDensity 0
    exact Erdos371CofactorDensity.density_zero_shift (S := B) hB
  have hD : D.HasDensity 0 := Erdos371ComparableRatio.fixed_ratio_hasDensity_zero 2
  have hU := Erdos371CofactorDensity.density_zero_union
    (Erdos371CofactorDensity.density_zero_union
      (Erdos371CofactorDensity.density_zero_union hA hB) hC) hD
  apply Erdos371Exploration.density_zero_of_subset (T := ((A∪B)∪C)∪D) _ hU
  intro n hn
  by_contra h
  simp only [Set.mem_union,not_or] at h
  have ha : ¬P n≤2 := h.1.1.1
  have hb : ¬1<tailRatio n := h.1.1.2
  have hc : ¬1<tailRatio (n+1) := h.1.2
  have hd : ¬max (P n) (P (n+1))≤2*min (P n) (P (n+1)) := h.2
  have hpn : P n≤n := Nat.maxPrimeFac_le
  exact hn ⟨by omega,le_of_not_gt hb,le_of_not_gt hc,by omega⟩

lemma primeSum_comparison_of_good {n : ℕ} (hg : comparisonGood n) :
    primeSum n<primeSum (n+1) ↔ P n<P (n+1) := by
  have hn := hg.1
  have hn1 : 1<n+1 := by omega
  by_cases h : P n<P (n+1)
  · have hh : 2*P n<P (n+1) := by
      simpa [min_eq_left h.le,max_eq_right h.le] using hg.2.2.2
    have hhr : 2*(P n:ℝ)<(P (n+1):ℝ) := by exact_mod_cast hh
    have hs : primeSum n<primeSum (n+1) :=
      (primeSum_upper hn hg.2.1).trans_lt (hhr.trans_le (primeSum_lower hn1))
    exact iff_of_true hs h
  · have hne := consecutive_ne n
    have hr : P (n+1)<P n := by omega
    have hh : 2*P (n+1)<P n := by
      simpa [min_eq_right hr.le,max_eq_left hr.le] using hg.2.2.2
    have hhr : 2*(P (n+1):ℝ)<(P n:ℝ) := by exact_mod_cast hh
    have hs : primeSum (n+1)<primeSum n :=
      (primeSum_upper hn1 hg.2.2.1).trans_lt (hhr.trans_le (primeSum_lower hn))
    exact iff_of_false (not_lt_of_gt hs) h

/-- The additive and largest-prime comparisons disagree only on a
natural-density-zero set. This does not determine their common density. -/
theorem comparison_disagreement_hasDensity_zero :
    {n | ¬(primeSum n<primeSum (n+1) ↔ P n<P (n+1))}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset (T := {n | ¬comparisonGood n}) _
    comparisonGood_complement_hasDensity_zero
  intro n hn hg
  exact hn (primeSum_comparison_of_good hg)

lemma comparison_indicator_difference_tendsto_zero :
    Tendsto (mean (fun n =>
      (if primeSum n<primeSum (n+1) then 1 else 0) -
      (if P n<P (n+1) then 1 else 0))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    comparisonGood_complement_hasDensity_zero
  · exact fun _ => abs_nonneg _
  · intro N
    change |mean (fun n =>
      (if primeSum n<primeSum (n+1) then 1 else 0) -
      (if P n<P (n+1) then 1 else 0)) N| ≤
      {n | ¬comparisonGood n}.partialDensity Set.univ N
    rw [← indicator_mean_eq_density]
    unfold mean
    rw [abs_div,show |(N:ℝ)|=(N:ℝ) from abs_of_nonneg (Nat.cast_nonneg N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    by_cases hg : comparisonGood n
    · simp only [Set.mem_setOf_eq,hg,not_true_eq_false,if_false,
        primeSum_comparison_of_good hg,sub_self,abs_zero,le_refl]
    · simp only [Set.mem_setOf_eq,hg,not_false_eq_true,if_true]
      split_ifs <;> norm_num

/-- An equivalent formulation of the original conjecture for a strongly
additive function. Neither half-density is asserted unconditionally. -/
theorem density_half_iff_primeSum :
    {n | P n<P (n+1)}.HasDensity (1/2) ↔
      {n | primeSum n<primeSum (n+1)}.HasDensity (1/2) := by
  have he := comparison_indicator_difference_tendsto_zero
  change Tendsto (fun N => mean (fun n =>
    (if primeSum n<primeSum (n+1) then 1 else 0) -
    (if P n<P (n+1) then 1 else 0)) N) atTop (𝓝 0) at he
  have hA (N : ℕ) : mean (fun n => if P n<P (n+1) then 1 else 0) N =
      {n | P n<P (n+1)}.partialDensity Set.univ N :=
    by
      rw [← indicator_mean_eq_density]
      congr 1
      funext n
      by_cases h : P n<P (n+1) <;> simp [h]
  have hB (N : ℕ) : mean (fun n => if primeSum n<primeSum (n+1) then 1 else 0) N =
      {n | primeSum n<primeSum (n+1)}.partialDensity Set.univ N :=
    indicator_mean_eq_density {n | primeSum n<primeSum (n+1)} N
  simp only [mean_sub,hA,hB] at he
  constructor
  · intro h
    have hh := h.add he
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.sub he
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring

end Erdos371AdditivePrimeDominance

#print axioms Erdos371AdditivePrimeDominance.tailRatio_mean_tendsto_zero
#print axioms Erdos371AdditivePrimeDominance.tailRatio_exception_hasDensity_zero

#print axioms Erdos371AdditivePrimeDominance.comparison_disagreement_hasDensity_zero
#print axioms Erdos371AdditivePrimeDominance.density_half_iff_primeSum
