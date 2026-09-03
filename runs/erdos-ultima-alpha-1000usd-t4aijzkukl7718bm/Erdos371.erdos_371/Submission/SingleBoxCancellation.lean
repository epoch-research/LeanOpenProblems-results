import Submission.UninflatedAllocationApproximation
import Submission.SmallPrimeReflectionDensity

/-! The uninflated signed limit for K=1 is elementary: away from the first
indices, the retained comparisons are precisely those just before a prime.
This case is too sparse to approximate the original comparison count. -/
namespace Erdos371
open Finset Filter RandomBins
open scoped Topology

namespace RandomBins
lemma primeAllocationRetention_one (X : ℝ) (n : ℕ) (hn : n ≠ 0) :
    primeAllocationRetention 1 X n = if (n : ℝ) ≤ X then 1 else 0 := by
  classical
  have hbox (a : PrimeAtomIndex n → Fin 1) (c : Fin 1) :
      boxProduct (primePowerAtom n) a c = n := by
    have ha : ∀ i, a i = c := fun i => Subsingleton.elim _ _
    simp only [boxProduct,ha,filter_true,prod_primePowerAtom n hn]
  by_cases hx : (n : ℝ) ≤ X
  · simp [primeAllocationRetention,hbox,hx,allocationWeight]
  · simp [primeAllocationRetention,hbox,hx,allocationWeight]
end RandomBins

lemma comparisonAllocationWeight_one_eq (N n : ℕ) (hn : 1 < n) :
    comparisonAllocationWeight 1 N 0 n = if (n+1).Prime then 1 else 0 := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by rw [← hwp]; exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  simp only [comparisonAllocationWeight,Real.rpow_zero,mul_one,
    primeAllocationRetention_one _ _ (by omega : losingNumber n ≠ 0),
    primeAllocationRetention_one _ _ hq.ne',Nat.cast_le]
  by_cases hprime : (n+1).Prime
  · have hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
      rw [hprime.maxPrimeFac_eq_self]
      exact Nat.maxPrimeFac_le.trans_lt (Nat.lt_succ_self n)
    have hwinner : primeWinner n = n+1 := by
      unfold primeWinner
      rw [max_eq_right hrise.le,hprime.maxPrimeFac_eq_self]
    have hlval : losingNumber n = n := if_pos hrise
    have hwval : winningNumber n = n+1 := if_pos hrise
    simp only [if_pos hprime,hlval,hwval,hwinner,Nat.div_self (by omega : 0 < n+1)]
    simp
  · have hlbig : primeWinner n < losingNumber n := by
      unfold losingNumber primeWinner
      split_ifs with h
      · rw [max_eq_right h.le]
        have hne : Nat.maxPrimeFac (n+1) ≠ n+1 := by
          intro he
          exact hprime (he ▸ Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega))
        have hlt : Nat.maxPrimeFac (n+1) < n+1 := lt_of_le_of_ne Nat.maxPrimeFac_le hne
        have hne' : Nat.maxPrimeFac (n+1) ≠ n := by
          intro he
          have hnp : n.Prime := he ▸ Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)
          rw [hnp.maxPrimeFac_eq_self,he] at h
          omega
        omega
      · rw [max_eq_left (not_lt.mp h)]
        exact Nat.maxPrimeFac_le.trans_lt (Nat.lt_succ_self n)
    simp only [if_neg hprime,if_neg (not_le_of_gt hlbig),zero_mul]

/-- On the retained one-box comparisons the sign is always positive. -/
lemma singleBox_signed_term (N n : ℕ) (hn : 1 < n) :
    factorSign n*comparisonAllocationWeight 1 N 0 n = if (n+1).Prime then 1 else 0 := by
  rw [comparisonAllocationWeight_one_eq N n hn]
  split_ifs with hp
  · have hrise : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
      rw [hp.maxPrimeFac_eq_self]
      exact Nat.maxPrimeFac_le.trans_lt (Nat.lt_succ_self n)
    simp only [factorSign,predicateSign,if_pos hrise,one_mul]
  · simp

lemma singleBox_weight_sum_bound (N : ℕ) :
    (∑ n ∈ range N, comparisonAllocationWeight 1 N 0 n) ≤
      2 + (((N+1).primesBelow).card : ℝ) := by
  classical
  have hpoint (n : ℕ) : comparisonAllocationWeight 1 N 0 n ≤
      (if n < 2 then (1 : ℝ) else 0) + (if (n+1).Prime then 1 else 0) := by
    by_cases hn : n < 2
    · have hw := (comparisonAllocationWeight_mem_unit 1 N (by omega) 0 n).2
      rw [if_pos hn]
      split_ifs <;> linarith
    · rw [comparisonAllocationWeight_one_eq N n (by omega),if_neg hn,zero_add]
  have hs := sum_le_sum (s := range N) fun n _ => hpoint n
  rw [sum_add_distrib] at hs
  have hsmall : (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) ≤ 2 := by
    have hc : ((range N).filter fun n => n < 2).card ≤ 2 := by
      apply (card_le_card _).trans_eq (card_range 2)
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  have hpr : (∑ n ∈ range N, if (n+1).Prime then (1 : ℝ) else 0) ≤
      (((N+1).primesBelow).card : ℝ) := by
    have hc : ((range N).filter fun n => (n+1).Prime).card ≤ ((N+1).primesBelow).card := by
      apply card_le_card_of_injOn (fun n => n+1)
      · intro n hn
        simp only [mem_coe] at hn ⊢
        obtain ⟨hn,hp⟩ := mem_filter.mp hn
        exact Nat.mem_primesBelow.mpr ⟨by have := mem_range.mp hn; omega,hp⟩
      · intro a ha b hb he
        dsimp only at he
        omega
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  linarith

/-- The unsigned one-box mass itself has vanishing mean. -/
theorem singleBox_weight_mean_tendsto_zero :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, comparisonAllocationWeight 1 N 0 n)/N)
      atTop (nhds 0) := by
  have ht := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add primesBelow_card_div_tendsto_zero
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n hn =>
    (comparisonAllocationWeight_mem_unit 1 N (by omega) 0 n).1) (Nat.cast_nonneg N)) _ ht
  intro N
  rw [← add_div]
  exact div_le_div_of_nonneg_right (singleBox_weight_sum_bound N) (Nat.cast_nonneg N)

/-- This establishes the signed-limit hypothesis for K=1 only. -/
theorem singleBox_signed_cancellation :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonAllocationWeight 1 N 0 n)/N) atTop (nhds 0) := by
  apply squeeze_zero_norm _ singleBox_weight_mean_tendsto_zero
  intro N
  rw [norm_div,Real.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [norm_mul,factorSign_norm,one_mul,Real.norm_eq_abs,
    abs_of_nonneg (comparisonAllocationWeight_mem_unit 1 N (by omega) 0 n).1]

/-- The same one-box case has asymptotic mean loss one, so it cannot supply
the approximation needed for the original conjecture. -/
theorem singleBox_mean_loss_tendsto_one :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (1-comparisonAllocationWeight 1 N 0 n))/N)
      atTop (nhds 1) := by
  have ht := singleBox_weight_mean_tendsto_zero.const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sub_div,
    div_self (by exact_mod_cast hN.ne')]

#print axioms singleBox_signed_cancellation
#print axioms singleBox_mean_loss_tendsto_one
end Erdos371
