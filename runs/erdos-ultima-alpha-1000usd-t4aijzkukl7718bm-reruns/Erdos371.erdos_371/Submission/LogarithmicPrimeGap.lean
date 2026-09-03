import FormalConjecturesUtil
import Submission.TwoThirdsPrimeGap

/-! An unconditional logarithmic strengthening of the small-gap estimate.
This file does not assert orientation balance. -/

namespace Erdos371LogarithmicPrimeGap

open Erdos371Cofactor Erdos371BoundedPrimeGap Erdos371DivisorGapSwitch
open Erdos371TerminalCompression Erdos371TwoThirdsPrimeGap
open Filter
open scoped Topology

def logGapSet : Set ℕ :=
  {n | Nat.dist (P n) (P (n+1)) * (Nat.log 2 (min (P n) (P (n+1))))^2 ≤
    min (P n) (P (n+1))}

def blockCover (k N : ℕ) : Finset ℕ :=
  cover (2^k) (2^(k+1)) (2^(k+1) / k^2) N

def logLowCover (K T N : ℕ) : Finset ℕ :=
  (Finset.Ico K T).biUnion fun k => blockCover k N

lemma four_pow (T : ℕ) : 4^T = (2^T)^2 := by
  rw [← pow_mul, Nat.mul_comm T 2, pow_mul]
  norm_num

lemma blockCover_card_bound {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ((blockCover k N).card : ℝ) ≤
      4 * (N:ℝ) / (k:ℝ)^2 + 8 * (4:ℝ)^k / (k:ℝ)^2 := by
  have h2 : (0:ℝ) < 2^k := by positivity
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hh := cover_card_bound (Nat.two_pow_pos k) (2^(k+1)) (2^(k+1)/k^2) N
  change ((blockCover k N).card : ℝ) ≤ _ at hh
  have hd : ((2^(k+1)/k^2:ℕ):ℝ) ≤ (2:ℝ)^(k+1)/(k:ℝ)^2 := by
    have hh := (Nat.cast_div_le (α := ℝ) (m := 2^(k+1)) (n := k^2))
    push_cast at hh
    exact hh
  calc
    _ ≤ 2 * ((2^(k+1)/k^2:ℕ):ℝ) * ((N:ℝ)/(2^k:ℕ) + (2^(k+1):ℕ)) := hh
    _ ≤ 2 * ((2:ℝ)^(k+1)/(k:ℝ)^2) * ((N:ℝ)/(2:ℝ)^k + (2:ℝ)^(k+1)) := by
      push_cast
      gcongr
    _ = _ := by
      have he : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
        rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
        norm_num
      rw [he, pow_succ]
      field_simp
      ring

lemma sum_four_pow_le (T : ℕ) : (∑ k ∈ Finset.range T, (4:ℝ)^k) ≤ 4^T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) T]

lemma logLowCover_card_bound {K : ℕ} (hK : 0 < K) (T N : ℕ) :
    ((logLowCover K T N).card : ℝ) ≤
      8 * (N:ℝ) / K + 8 * (4:ℝ)^T / (K:ℝ)^2 := by
  have hK' : (0:ℝ) < K := Nat.cast_pos.mpr hK
  have hs : (∑ k ∈ Finset.Ico K T, (4:ℝ)^k/(k:ℝ)^2) ≤ (4:ℝ)^T/(K:ℝ)^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico K T, (4:ℝ)^k/(K:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hkk : (K:ℝ) ≤ k := Nat.cast_le.mpr (Finset.mem_Ico.mp hk).1
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hK')
          (by nlinarith)
      _ = (∑ k ∈ Finset.Ico K T, (4:ℝ)^k)/(K:ℝ)^2 := (Finset.sum_div ..).symm
      _ ≤ (∑ k ∈ Finset.range T, (4:ℝ)^k)/(K:ℝ)^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        · intros; positivity
      _ ≤ _ := div_le_div_of_nonneg_right (sum_four_pow_le T) (sq_nonneg _)
  have hc : (logLowCover K T N).card ≤
      ∑ k ∈ Finset.Ico K T, (blockCover k N).card := Finset.card_biUnion_le
  calc
    _ ≤ ∑ k ∈ Finset.Ico K T, ((blockCover k N).card:ℝ) := by exact_mod_cast hc
    _ ≤ ∑ k ∈ Finset.Ico K T, (4*(N:ℝ)/(k:ℝ)^2 + 8*(4:ℝ)^k/(k:ℝ)^2) :=
      Finset.sum_le_sum (fun k hk => blockCover_card_bound
        (hK.trans_le (Finset.mem_Ico.mp hk).1) N)
    _ = 4*(N:ℝ) * (∑ k ∈ Finset.Ico K T, 1/(k:ℝ)^2) +
        8 * (∑ k ∈ Finset.Ico K T, (4:ℝ)^k/(k:ℝ)^2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 4*(N:ℝ)*(2/(K:ℝ)) + 8*((4:ℝ)^T/(K:ℝ)^2) := by
      gcongr
      exact sum_reciprocal_sq hK T
    _ = _ := by ring

lemma low_gap_in_logLowCover {K T n N : ℕ} (hn : 3 ≤ n) (hnN : n < N)
    (hgap : n ∈ logGapSet) (hlo : 2^K ≤ min (P n) (P (n+1)))
    (hhi : min (P n) (P (n+1)) < 2^T) (hK : 0 < K) :
    n ∈ logLowCover K T N := by
  let q := min (P n) (P (n+1))
  let c := Nat.dist (P n) (P (n+1))
  let k := Nat.log 2 q
  have hKk : K ≤ k := Nat.le_log_of_pow_le (by decide) hlo
  have hk0 : 0 < k := hK.trans_le hKk
  have hq0 : q ≠ 0 := by
    have hh := Nat.two_pow_pos K
    omega
  have hkT : k < T := Nat.log_lt_of_lt_pow hq0 hhi
  have hkq : 2^k ≤ q := Nat.pow_log_le_self _ hq0
  have hqk : q < 2^(k+1) := Nat.lt_pow_succ_log_self (by decide) q
  have hc : c ≤ 2^(k+1)/k^2 := by
    apply (Nat.le_div_iff_mul_le (Nat.pow_pos hk0)).mpr
    exact (show c*k^2 ≤ q from hgap).trans hqk.le
  have hc0 : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro he
    exact Erdos371PrimeDiscrepancy.consecutive_ne n (Nat.eq_of_dist_eq_zero he).symm
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_Ico.mpr ⟨hKk,hkT⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨q, Finset.mem_Ico.mpr ⟨hkq,hqk⟩, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨c, Finset.mem_Icc.mpr ⟨hc0,hc⟩, own_primePair_mem hn hnN⟩

lemma sq_lt_two_pow {T : ℕ} (hT : 5 ≤ T) : T^2 < 2^T := by
  induction T, hT using Nat.le_induction with
  | base => norm_num
  | succ T hT ih =>
    rw [pow_succ (2:ℕ) T]
    nlinarith

lemma high_gap_in_logSwitch {T n : ℕ} (hT : 5 ≤ T) (hn : 3 ≤ n)
    (hnN : n < 4^T) (hgap : n ∈ logGapSet)
    (hhigh : 2^T ≤ min (P n) (P (n+1))) :
    n ∈ switchCover (2^T) (T^2) (4^T) := by
  apply mem_switchCover_of_close hn hnN (by positivity : 0 < T^2)
  · have hpn : 2^T ≤ P n := hhigh.trans (min_le_left _ _)
    have hnprod := cofactor_mul n
    have hmul := Nat.mul_le_mul_left (cofactor n) hpn
    have hc : cofactor n ≤ 2^T := by
      rw [four_pow] at hnN
      nlinarith [Nat.two_pow_pos T]
    exact (min_le_left _ _).trans hc
  · exact (sq_lt_two_pow hT).trans_le hhigh
  · have htlog : T ≤ Nat.log 2 (min (P n) (P (n+1))) :=
      Nat.le_log_of_pow_le (by decide) hhigh
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htlog 2)).trans hgap

lemma geometric_density_bound {K T : ℕ} (hK : 0 < K) (hT : 5 ≤ T) :
    logGapSet.partialDensity Set.univ (4^T) ≤
      3 / (4^T:ℕ) + (lowSet (2^K)).partialDensity Set.univ (4^T) +
      8/(K:ℝ) + 8/(K:ℝ)^2 + 2*H (2^T)/(T:ℝ)^2 + 2/(T:ℝ)^2 := by
  let N := 4^T
  let G := (Finset.range N).filter (fun n =>
    Nat.dist (P n) (P (n+1)) * (Nat.log 2 (min (P n) (P (n+1))))^2 ≤
      min (P n) (P (n+1)))
  let L := (Finset.range N).filter (fun n => P n ≤ 2^K ∨ P (n+1) ≤ 2^K)
  have hsub : G ⊆ ((Finset.range 3 ∪ L) ∪ logLowCover K T N) ∪
      switchCover (2^T) (T^2) N := by
    intro n hn
    obtain ⟨hnN,hg⟩ := Finset.mem_filter.mp hn
    have hnN' := Finset.mem_range.mp hnN
    by_cases hn3 : n < 3
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_range.mpr hn3)))
    by_cases hlo : P n ≤ 2^K ∨ P (n+1) ≤ 2^K
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnN,hlo⟩)))
    by_cases hhi : min (P n) (P (n+1)) < 2^T
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (low_gap_in_logLowCover (by omega) hnN' hg (by omega) hhi hK))
    · exact Finset.mem_union_right _ (high_gap_in_logSwitch hT (by omega) hnN' hg (by omega))
  have hc : G.card ≤ 3 + L.card + (logLowCover K T N).card +
      (switchCover (2^T) (T^2) N).card := by
    have h0 := Finset.card_le_card hsub
    have h1 := Finset.card_union_le ((Finset.range 3 ∪ L) ∪ logLowCover K T N)
      (switchCover (2^T) (T^2) N)
    have h2 := Finset.card_union_le (Finset.range 3 ∪ L) (logLowCover K T N)
    have h3 := Finset.card_union_le (Finset.range 3) L
    simp only [Finset.card_range] at h3
    omega
  have hc' : (G.card:ℝ) ≤ 3 + L.card + (logLowCover K T N).card +
      (switchCover (2^T) (T^2) N).card := by exact_mod_cast hc
  have hlow := logLowCover_card_bound hK T N
  have hswitch := switchCover_card_bound (by positivity : 0 < T^2) (2^T) N
  have hg : logGapSet.partialDensity Set.univ N = (G.card:ℝ)/N := partialDensity_filter _ _
  have hl : (lowSet (2^K)).partialDensity Set.univ N = (L.card:ℝ)/N := partialDensity_filter _ _
  rw [hg,hl]
  have ht : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk : (K:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfour : (4:ℝ)^T = ((2:ℝ)^T)^2 := by exact_mod_cast four_pow T
  calc
    _ ≤ (3 + L.card + (8*(N:ℝ)/K + 8*(4:ℝ)^T/(K:ℝ)^2) +
        (2*(N:ℝ)/(T^2:ℕ)*H (2^T) + 2*((2^T:ℕ):ℝ)^2/(T^2:ℕ))) / N :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = _ := by
      dsimp [N]
      push_cast
      rw [hfour]
      field_simp
      ring

lemma harmonic_geometric_div_sq_tendsto_zero :
    Tendsto (fun T : ℕ => H (2^T)/(T:ℝ)^2) atTop (𝓝 0) := by
  have hsq : Tendsto (fun T : ℕ => 1/(T:ℝ)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp
      (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  have hu : Tendsto (fun T : ℕ => 1/(T:ℝ)^2 + Real.log 2 / T) atTop (𝓝 0) := by
    simpa using hsq.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun T => div_nonneg (H_nonneg _) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with T hT
    have ht : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    have hh := H_le_log (2^T)
    push_cast at hh
    rw [Real.log_pow] at hh
    calc
      _ ≤ (1 + (T:ℝ)*Real.log 2)/(T:ℝ)^2 :=
        div_le_div_of_nonneg_right hh (sq_nonneg _)
      _ = _ := by field_simp

lemma log_gap_density_geometric :
    Tendsto (fun T : ℕ => logGapSet.partialDensity Set.univ (4^T)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsmall : Tendsto (fun K : ℕ => 8/(K:ℝ) + 8/(K:ℝ)^2) atTop (𝓝 0) := by
    have hsq : Tendsto (fun K : ℕ => 8/(K:ℝ)^2) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat (8:ℝ)).comp
        (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (8:ℝ)).add hsq
  obtain ⟨K,hK,hsmallK⟩ := ((eventually_gt_atTop 0).and
    (hsmall.eventually (gt_mem_nhds (half_pos hε)))).exists
  have hp : Tendsto (fun T : ℕ => 4^T) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hsq : Tendsto (fun T : ℕ => 2/(T:ℝ)^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_pow] using (tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp
      (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0))
  have hu : Tendsto (fun T : ℕ => 3/(4^T:ℕ) +
      (lowSet (2^K)).partialDensity Set.univ (4^T) +
      2*(H (2^T)/(T:ℝ)^2) + 2/(T:ℝ)^2) atTop (𝓝 0) := by
    simpa using ((((tendsto_const_div_atTop_nhds_zero_nat (3:ℝ)).comp hp).add
      ((lowSet_hasDensity_zero (2^K)).comp hp)).add
      (tendsto_const_nhds.mul harmonic_geometric_div_sq_tendsto_zero)).add hsq
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max T₀ 5, fun T hT => ?_⟩
  have hb := geometric_density_bound hK (by omega : 5 ≤ T)
  have hh := hT₀ T (by omega)
  change 8/(K:ℝ) + 8/(K:ℝ)^2 < ε/2 at hsmallK
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  simp only [mul_div_assoc] at hb
  linarith

lemma exists_geometric_bracket {N : ℕ} (hN : 1 < N) :
    ∃ T : ℕ, 0 < T ∧ N ≤ 4^T ∧ 4^T ≤ 4*N := by
  let T := Nat.clog 4 N
  have hNT : N ≤ 4^T := Nat.le_pow_clog (by decide) N
  have hT : 0 < T := by
    by_contra hh
    have he : T = 0 := by omega
    simp [he] at hNT
    omega
  refine ⟨T,hT,hNT,?_⟩
  have hlo : 4^(T-1) < N := Nat.pow_pred_clog_lt_self (by decide) hN
  have he : 4^T = 4^(T-1)*4 := by
    calc
      _ = 4^((T-1)+1) := congrArg (4^·) (by omega)
      _ = _ := pow_succ ..
  rw [he]
  omega

lemma hasDensity_zero_of_geometric (S : Set ℕ)
    (h : Tendsto (fun T : ℕ => S.partialDensity Set.univ (4^T)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  rw [Set.HasDensity, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds (show 0 < ε/4 by positivity)))
  have hp0 : 0 < (4:ℕ)^T₀ := by positivity
  refine ⟨4^T₀+2, fun N hN => ?_⟩
  obtain ⟨T,hT,hNT,hTN⟩ := exists_geometric_bracket (N := N) (by omega)
  have hTbig : T₀ ≤ T := by
    by_contra hh
    have hb := Nat.pow_le_pow_right (by decide : 0 < 4) (show T ≤ T₀ by omega)
    omega
  have hs := hT₀ T hTbig
  have hb : S.partialDensity Set.univ N ≤ 4 * S.partialDensity Set.univ (4^T) := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hm : (0:ℝ) < (4^T:ℕ) := Nat.cast_pos.mpr (by positivity)
    have hc : (S ∩ Set.Iio N).ncard ≤ (S ∩ Set.Iio (4^T)).ncard :=
      Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hNT))
    have hr : ((4^T:ℕ):ℝ) / N ≤ 4 := (div_le_iff₀ hn).mpr (by exact_mod_cast hTN)
    calc
      _ ≤ ((S ∩ Set.Iio (4^T)).ncard:ℝ) / N :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hc) hn.le
      _ = (((S ∩ Set.Iio (4^T)).ncard:ℝ) / (4^T:ℕ)) * (((4^T:ℕ):ℝ) / N) := by field_simp
      _ ≤ (((S ∩ Set.Iio (4^T)).ncard:ℝ) / (4^T:ℕ)) * 4 :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold Set.partialDensity; positivity)]
  linarith

/-- A logarithmic separation estimate. It supplies no orientation information. -/
theorem logarithmic_prime_gap_hasDensity_zero : logGapSet.HasDensity 0 :=
  hasDensity_zero_of_geometric _ log_gap_density_geometric

end Erdos371LogarithmicPrimeGap

#print axioms Erdos371LogarithmicPrimeGap.logarithmic_prime_gap_hasDensity_zero
