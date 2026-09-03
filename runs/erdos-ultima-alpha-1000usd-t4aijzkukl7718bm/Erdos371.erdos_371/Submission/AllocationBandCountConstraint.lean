import Submission.ComparisonBandTuples

/-! The number of boxes and a fixed positive power lower cutoff cannot both
remain large. The resulting vanishing signed limit is sparse and does not
supply the approximation required by the density conjecture. -/
namespace Erdos371
open Finset Filter RandomBins
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace RandomBins

lemma primeAllocationBandRetention_zero_of_product_lt (K n : ℕ) (hn : n ≠ 0)
    (Y X : ℝ) (hY : 0 ≤ Y) (hsize : (n : ℝ) < Y^K) :
    primeAllocationBandRetention K Y X n = 0 := by
  unfold primeAllocationBandRetention
  apply sum_eq_zero
  intro a ha
  have hprod := prod_le_prod (s := univ) (f := fun _ : Fin K => Y)
    (g := fun c => (boxProduct (primePowerAtom n) a c : ℝ))
    (fun c _ => hY) (fun c _ => ((mem_filter.mp ha).2 c).1)
  simp only [prod_const,card_univ,Fintype.card_fin] at hprod
  rw [← Nat.cast_prod,prod_boxProduct,prod_primePowerAtom n hn] at hprod
  exact False.elim (hsize.not_ge hprod)

lemma primeAllocationBandRetention_pos_lower (K n : ℕ) (hn : n ≠ 0)
    (Y X : ℝ) (hY : 0 ≤ Y) (hret : 0 < primeAllocationBandRetention K Y X n) :
    Y^K ≤ (n : ℝ) := by
  by_contra h
  rw [primeAllocationBandRetention_zero_of_product_lt K n hn Y X hY (lt_of_not_ge h)] at hret
  exact (lt_irrefl _ hret)

end RandomBins

/-- Every retained comparison needs K*eta<1, since the winning cofactor is
strictly below N and is a product of K boxes of size at least N^eta. -/
theorem comparisonBandAllocationWeight_pos_exponent (K N n : ℕ) (η : ℝ)
    (hN : 1 < N) (hn : 1 < n) (hnN : n < N)
    (hW : 0 < comparisonBandAllocationWeight K N η n) : (K : ℝ)*η < 1 := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by
    rw [← hwp]
    exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n/primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have hqN : winningNumber n/primeWinner n < N :=
    (Nat.div_lt_self (by omega : 0 < winningNumber n) hp.one_lt).trans_le (by omega)
  have hB := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n)
    (winningNumber n/primeWinner n)
  have hBpos : 0 < primeAllocationBandRetention K ((N : ℝ)^η) (primeWinner n)
      (winningNumber n/primeWinner n) := by
    unfold comparisonBandAllocationWeight at hW
    rcases mul_pos_iff.mp hW with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge hB.1) h.2)
  have hlower := primeAllocationBandRetention_pos_lower K (winningNumber n/primeWinner n)
    hq.ne' ((N : ℝ)^η) (primeWinner n) (Real.rpow_nonneg (Nat.cast_nonneg N) η) hBpos
  have he : ((N : ℝ)^η)^K = (N : ℝ)^((K : ℝ)*η) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  rw [he] at hlower
  have hlt : (N : ℝ)^((K : ℝ)*η) < (N : ℝ)^(1 : ℝ) := by
    rw [Real.rpow_one]
    exact hlower.trans_lt (by exact_mod_cast hqN)
  exact (Real.rpow_lt_rpow_left_iff (show (1 : ℝ) < (N : ℝ) by exact_mod_cast hN)).mp hlt

lemma comparisonBandAllocationWeight_zero_of_exponent (K N n : ℕ) (hK : 0 < K)
    (η : ℝ) (hN : 1 < N) (hn : 1 < n) (hnN : n < N) (hsize : 1 ≤ (K : ℝ)*η) :
    comparisonBandAllocationWeight K N η n = 0 := by
  apply le_antisymm _ (comparisonBandAllocationWeight_bounds K N hK η n).1
  by_contra h
  exact hsize.not_gt (comparisonBandAllocationWeight_pos_exponent K N n η hN hn hnN (lt_of_not_ge h))

lemma comparisonBandAllocationWeight_large_box_count_sum (K N : ℕ) (hK : 0 < K)
    (η : ℝ) (hN : 1 < N) (hsize : 1 ≤ (K : ℝ)*η) :
    (∑ n ∈ range N, comparisonBandAllocationWeight K N η n) ≤ 2 := by
  have hpoint (n : ℕ) (hn : n ∈ range N) : comparisonBandAllocationWeight K N η n ≤
      if n < 2 then (1 : ℝ) else 0 := by
    by_cases hsmall : n < 2
    · rw [if_pos hsmall]
      exact (comparisonBandAllocationWeight_bounds K N hK η n).2.trans
        (comparisonAllocationWeight_mem_unit K N hK 0 n).2
    · rw [if_neg hsmall,comparisonBandAllocationWeight_zero_of_exponent K N n hK η hN
        (by omega) (mem_range.mp hn) hsize]
  have hs := sum_le_sum hpoint
  have hc : ((range N).filter fun n => n < 2).card ≤ 2 := by
    apply (card_le_card _).trans_eq (card_range 2)
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  have hsmall : (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) ≤ 2 := by
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  exact hs.trans hsmall

/-- At a fixed positive lower exponent, any box count tending to infinity
retains vanishing mean mass. This is the opposite of the desired approximation. -/
theorem growingBoxCount_band_weight_tendsto_zero (K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, comparisonBandAllocationWeight (K N) N η n)/N)
      atTop (nhds 0) := by
  have hprod := (tendsto_natCast_atTop_atTop.comp hK).atTop_mul_const hη
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hK.eventually_gt_atTop 0,hprod.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℕ),ht.eventually_lt_const hε] with N hKpos hsize hN ht
  have hnonneg : 0 ≤ (∑ n ∈ range N, comparisonBandAllocationWeight (K N) N η n)/N :=
    div_nonneg (sum_nonneg fun n hn => (comparisonBandAllocationWeight_bounds (K N) N hKpos η n).1)
      (Nat.cast_nonneg N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  exact (div_le_div_of_nonneg_right
    (comparisonBandAllocationWeight_large_box_count_sum (K N) N hKpos η hN hsize)
      (Nat.cast_nonneg (α := ℝ) N)).trans_lt ht

/-- Signed cancellation here follows only because all retained mass disappears. -/
theorem growingBoxCount_band_signed_tendsto_zero (K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonBandAllocationWeight (K N) N η n)/N)
      atTop (nhds 0) := by
  have ht := growingBoxCount_band_weight_tendsto_zero K hK η hη
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hK.eventually_gt_atTop 0,ht.eventually_lt_const hε] with N hKpos ht
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  apply lt_of_le_of_lt _ ht
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul,show |factorSign n| = 1 by simpa only [Real.norm_eq_abs] using factorSign_norm n,
    one_mul,abs_of_nonneg (comparisonBandAllocationWeight_bounds (K N) N hKpos η n).1]

/-- The mean approximation loss tends to one, so this signed case cannot be
substituted into the density criterion with fixed K and small eta. -/
theorem growingBoxCount_band_mean_loss_tendsto_one (K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (1-comparisonBandAllocationWeight (K N) N η n))/N)
      atTop (nhds 1) := by
  have ht := (growingBoxCount_band_weight_tendsto_zero K hK η hη).const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sub_div,
    div_self (by exact_mod_cast hN.ne')]

#print axioms comparisonBandAllocationWeight_pos_exponent
#print axioms growingBoxCount_band_signed_tendsto_zero
#print axioms growingBoxCount_band_mean_loss_tendsto_one
end Erdos371
