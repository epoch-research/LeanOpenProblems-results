import Submission.ComparisonAtomBuffers
import Submission.ClippedLogCriterion
import Submission.PrimeReflectionBoundary

/-! Uniform mean approximation with box cutoff exactly the winning prime.
The former positive inflation is no longer needed. The signed limit at the end
is still a hypothesis, not a proved arithmetic estimate. -/
namespace Erdos371
open Finset Filter RandomBins FiniteSieve
open scoped Topology
attribute [local instance] Classical.propDecidable

private lemma neighbor_indicator_sum_bound (P : ℕ → Prop) (N : ℕ) :
    (∑ n ∈ range N, if P n ∨ P (n+1) then (1 : ℝ) else 0) ≤
      2*((((range N).filter fun n => P (n+1)).card : ℝ)) + 1 := by
  have hsub : (range N).filter (fun n => P n ∨ P (n+1)) ⊆
      (range N).filter P ∪ (range N).filter (fun n => P (n+1)) := by
    intro n hn
    obtain ⟨hn,h | h⟩ := mem_filter.mp hn
    · exact mem_union_left _ (mem_filter.mpr ⟨hn,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,h⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hshift := filter_count_le_shifted_add_one P N
  have hh : ((range N).filter (fun n => P n ∨ P (n+1))).card ≤
      2*((range N).filter (fun n => P (n+1))).card+1 := by omega
  simpa only [sum_boole,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
    (Nat.cast_le (α := ℝ)).mpr hh

lemma comparisonAllocationWeight_zero_point_bound (K N n : ℕ) (hK : 0 < K) (hN : 1 < N)
    (hnN : n < N) (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hηv : η ≤ v/2) :
    1-comparisonAllocationWeight K N 0 n ≤
      (if n < 2 then (1 : ℝ) else 0) +
      (if (primeWinner n : ℝ) ≤ (N : ℝ)^v then 1 else 0) +
      (if logRatioEvent N η n then 1 else 0) +
      (if largeRepeatedAtom ((N : ℝ)^η) n ∨ largeRepeatedAtom ((N : ℝ)^η) (n+1) then 1 else 0) +
      (if sameIntegerPrimeGapEvent N v η n ∨ sameIntegerPrimeGapEvent N v η (n+1) then 1 else 0) +
      2/((K : ℝ)*v*η) := by
  have hW := comparisonAllocationWeight_mem_unit K N hK 0 n
  have hC : 0 ≤ 2/((K : ℝ)*v*η) := by positivity
  by_cases hbad : n < 2 ∨ (primeWinner n : ℝ) ≤ (N : ℝ)^v ∨ logRatioEvent N η n ∨
      (largeRepeatedAtom ((N : ℝ)^η) n ∨ largeRepeatedAtom ((N : ℝ)^η) (n+1)) ∨
      (sameIntegerPrimeGapEvent N v η n ∨ sameIntegerPrimeGapEvent N v η (n+1))
  · have hI : (1 : ℝ) ≤ (if n < 2 then 1 else 0) +
        (if (primeWinner n : ℝ) ≤ (N : ℝ)^v then 1 else 0) +
        (if logRatioEvent N η n then 1 else 0) +
        (if largeRepeatedAtom ((N : ℝ)^η) n ∨ largeRepeatedAtom ((N : ℝ)^η) (n+1) then 1 else 0) +
        (if sameIntegerPrimeGapEvent N v η n ∨ sameIntegerPrimeGapEvent N v η (n+1) then 1 else 0) := by
      split_ifs <;> norm_num <;> tauto
    linarith
  · push_neg at hbad
    obtain ⟨hn,hp,hclose,⟨hr,hr'⟩,⟨hg,hg'⟩⟩ := hbad
    have hgw : ¬sameIntegerPrimeGapEvent N v η (winningNumber n) := by
      unfold winningNumber
      split_ifs <;> assumption
    have h := comparisonAllocationWeight_zero_loss K N n hK hN (by omega) hnN v η hv hη hηv
      hp.le hclose hr hr' hgw
    simpa only [if_neg (by omega : ¬n < 2),if_neg (not_le_of_gt hp),if_neg hclose,
      if_neg (not_or.mpr ⟨hr,hr'⟩),if_neg (not_or.mpr ⟨hg,hg'⟩),zero_add] using h

lemma comparisonAllocationWeight_zero_mean_bound (K N : ℕ) (hK : 0 < K) (hN : 1 < N)
    (v η : ℝ) (hv : 0 < v) (hη : 0 < η) (hηv : η ≤ v/2) :
    (∑ n ∈ range N, (1-comparisonAllocationWeight K N 0 n))/N ≤
      4/N + (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ)/N +
      ((logRatioSet N η).card : ℝ)/N + 2*((largeRepeatedAtomSet N η).card : ℝ)/N +
      2*((sameIntegerPrimeGapSet N v η).card : ℝ)/N + 2/((K : ℝ)*v*η) := by
  have hs := sum_le_sum (s := range N) fun n hn =>
    comparisonAllocationWeight_zero_point_bound K N n hK hN (mem_range.mp hn) v η hv hη hηv
  simp only [sum_add_distrib,sum_const,card_range,nsmul_eq_mul] at hs
  have hsmall : (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) ≤ 2 := by
    have hc : ((range N).filter fun n => n < 2).card ≤ 2 := by
      apply (card_le_card _).trans_eq (card_range 2)
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  have hlow : (∑ n ∈ range N, if (primeWinner n : ℝ) ≤ (N : ℝ)^v then (1 : ℝ) else 0) ≤
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ) := by
    have hc : ((range N).filter fun n => (primeWinner n : ℝ) ≤ (N : ℝ)^v) ⊆
        ((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v) := by
      intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      have hle : Nat.maxPrimeFac (n+1) ≤ primeWinner n := le_max_right _ _
      exact mem_filter.mpr ⟨hn,(show (Nat.maxPrimeFac (n+1) : ℝ) ≤ primeWinner n by
        exact_mod_cast hle).trans hp⟩
    simpa using (Nat.cast_le (α := ℝ)).mpr (card_le_card hc)
  have hclose : (∑ n ∈ range N, if logRatioEvent N η n then (1 : ℝ) else 0) =
      (logRatioSet N η).card := by simp [logRatioSet]
  have hrep := neighbor_indicator_sum_bound (largeRepeatedAtom ((N : ℝ)^η)) N
  change (∑ n ∈ range N, if largeRepeatedAtom ((N : ℝ)^η) n ∨
    largeRepeatedAtom ((N : ℝ)^η) (n+1) then (1 : ℝ) else 0) ≤
      2*((largeRepeatedAtomSet N η).card : ℝ)+1 at hrep
  have hgap := neighbor_indicator_sum_bound (sameIntegerPrimeGapEvent N v η) N
  change (∑ n ∈ range N, if sameIntegerPrimeGapEvent N v η n ∨
    sameIntegerPrimeGapEvent N v η (n+1) then (1 : ℝ) else 0) ≤
      2*((sameIntegerPrimeGapSet N v η).card : ℝ)+1 at hgap
  have hb : (∑ n ∈ range N, (1-comparisonAllocationWeight K N 0 n)) ≤
      4 + (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^v).card : ℝ) +
      (logRatioSet N η).card + 2*((largeRepeatedAtomSet N η).card : ℝ) +
      2*((sameIntegerPrimeGapSet N v η).card : ℝ) + (N : ℝ)*(2/((K : ℝ)*v*η)) := by linarith
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  convert hd using 1
  field_simp

/-- Uniform approximation with cutoff exactly p (no inflation). The count of
boxes K is fixed before N tends to infinity. -/
theorem comparisonAllocationWeight_zero_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (1-comparisonAllocationWeight K N 0 n))/N < ε := by
  let v : ℝ := min 1 (ε/640)
  have hv : 0 < v := lt_min (by norm_num) (by positivity)
  have hv1 : v ≤ 1 := min_le_left _ _
  have hve : v ≤ ε/640 := min_le_right _ _
  have hvsmall : 80*v^2 ≤ ε/8 := by
    have hh := (le_div_iff₀ (by norm_num : (0 : ℝ) < 640)).mp hve
    nlinarith
  obtain ⟨η₀,hη₀,hclose⟩ := logRatioSet_uniform_rarity (ε/8) (by positivity)
  let η : ℝ := min η₀ (min (v/2) (ε*v^2/4096))
  have hη : 0 < η := lt_min hη₀ (lt_min (by positivity) (by positivity))
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hηv : η ≤ v/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηe : η ≤ ε*v^2/4096 := (min_le_right _ _).trans (min_le_right _ _)
  have hgsmall : 128*η/v^2 ≤ ε/32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hv)).mpr
    nlinarith
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1 : ℝ) (16/(ε*(v*η))))
  have hKpos : 0 < K := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans hK.le))
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hlarge : 16 < (K : ℝ)*(ε*(v*η)) :=
    (div_lt_iff₀ (by positivity)).mp ((le_max_right _ _).trans_lt hK)
  have hC : 2/((K : ℝ)*v*η) < ε/8 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)).add
    ((largeRepeatedAtomSet_ratio_tendsto_zero η hη).const_mul 2)
  simp only [mul_zero,add_zero] at ht
  have hs := smooth_power_count_eventually_le v hv.le (ε/8) (by positivity)
  have hg := sameIntegerPrimeGapSet_eventually_le v η hv hv1 hη.le hηv (ε/32) (by positivity)
  refine ⟨K,hKpos,?_⟩
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity),hs,hg,hclose,
    eventually_gt_atTop (1 : ℕ)] with N ht hs hg hc hN
  have hclose' : ((logRatioSet N η).card : ℝ)/N ≤ ε/8 :=
    (div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr
      (card_le_card (logRatioSet_mono_width N η η₀ hN.le hη₀'))) (Nat.cast_nonneg N)).trans hc
  have hb := comparisonAllocationWeight_zero_mean_bound K N hKpos hN v η hv hη hηv
  simp only [mul_div_assoc] at hb ht
  linarith

/-- The uninflated signed criterion. The hypothesis remains unproved. -/
theorem density_of_uninflatedAllocation_cancellation
    (hcancel : ∀ K : ℕ, 0 < K → Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonAllocationWeight K N 0 n)/N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,ha⟩ := comparisonAllocationWeight_zero_uniform_approximation (ε/2) (by positivity)
  have hc := Metric.tendsto_nhds.mp (hcancel K hK) (ε/2) (by positivity)
  filter_upwards [ha,hc] with N ha hc
  rw [Real.dist_eq,sub_zero] at hc ⊢
  have hb := comparisonAllocationWeight_signed_error_bound K N hK 0
  have ht := abs_sub_le ((∑ n ∈ range N, factorSign n)/N)
    ((∑ n ∈ range N, factorSign n*comparisonAllocationWeight K N 0 n)/N) 0
  simp only [sub_zero] at ht
  linarith

#print axioms comparisonAllocationWeight_zero_uniform_approximation
#print axioms density_of_uninflatedAllocation_cancellation
end Erdos371
