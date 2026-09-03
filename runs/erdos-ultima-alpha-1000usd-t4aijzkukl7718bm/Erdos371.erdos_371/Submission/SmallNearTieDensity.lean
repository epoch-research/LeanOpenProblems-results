import Submission.ComparablePrimeMass
import Submission.LargeNearTieDensity
import Submission.GapExplore

/-! The below-square-root portion of fixed-ratio near ties has natural
density zero, by the CRT and the comparable-prime reciprocal tail. -/

namespace Erdos371
namespace FiniteSieve
open Finset Filter

def factorRatioEvent (C n : ℕ) : Prop :=
  Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1) ∧
    Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n

instance (C n : ℕ) : Decidable (factorRatioEvent C n) := inferInstanceAs (Decidable (_ ∧ _))

def smallPrimeRatioSet (N C A D : ℕ) : Finset ℕ :=
  (range N).filter fun n => 1 < n ∧ Nat.maxPrimeFac n ∈ primesAbovePower A D ∧
    Nat.maxPrimeFac (n+1) ∈ primesAbovePower A D ∧ factorRatioEvent C n

lemma primesAbovePower_card_le (A D : ℕ) : (primesAbovePower A D).card ≤ D := by
  have hs : primesAbovePower A D ⊆ Icc 1 D := by
    intro p hp
    obtain ⟨hpp,_,hpD⟩ := mem_primesAbovePower.mp hp
    exact mem_Icc.mpr ⟨hpp.one_le,hpD⟩
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hs

lemma smallPrimeRatioSet_card_sum_le (N C A D : ℕ) :
    (smallPrimeRatioSet N C A D).card ≤
      ∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
        if p ≤ C*q ∧ q ≤ C*p then ((range N).filter fun n => p ∣ n ∧ q ∣ n+1).card else 0 := by
  let S := primesAbovePower A D
  have hs : smallPrimeRatioSet N C A D ⊆ S.biUnion (fun p => S.biUnion (fun q =>
      if p ≤ C*q ∧ q ≤ C*p then (range N).filter (fun n => p ∣ n ∧ q ∣ n+1) else ∅)) := by
    intro n hn
    obtain ⟨hnN,_,hp,hq,hcomp⟩ := mem_filter.mp hn
    refine mem_biUnion.mpr ⟨Nat.maxPrimeFac n,hp,mem_biUnion.mpr ⟨Nat.maxPrimeFac (n+1),hq,?_⟩⟩
    change Nat.maxPrimeFac n ≤ C*Nat.maxPrimeFac (n+1) ∧ Nat.maxPrimeFac (n+1) ≤ C*Nat.maxPrimeFac n at hcomp
    rw [if_pos hcomp]
    exact mem_filter.mpr ⟨hnN,Nat.maxPrimeFac_dvd,Nat.maxPrimeFac_dvd⟩
  refine (card_le_card hs).trans (card_biUnion_le.trans (sum_le_sum fun p hp => ?_))
  refine card_biUnion_le.trans_eq ?_
  apply sum_congr rfl
  intro q hq
  split_ifs <;> simp

lemma smallPrimeRatioSet_card_le (N C A D : ℕ) :
    ((smallPrimeRatioSet N C A D).card : ℝ) ≤ N*comparablePrimeMass C A D + (D : ℝ)^2 := by
  have hcount := (Nat.cast_le (α := ℝ)).mpr (smallPrimeRatioSet_card_sum_le N C A D)
  push_cast at hcount
  have hsum : (∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
      if p ≤ C*q ∧ q ≤ C*p then (((range N).filter fun n => p ∣ n ∧ q ∣ n+1).card : ℝ) else 0) ≤
        N*comparablePrimeMass C A D + ((primesAbovePower A D).card : ℝ)^2 := by
    calc
      _ ≤ ∑ p ∈ primesAbovePower A D, ∑ q ∈ primesAbovePower A D,
          (N*(if p ≤ C*q ∧ q ≤ C*p then (1 : ℝ)/((p : ℝ)*q) else 0)+1) := by
        apply sum_le_sum
        intro p hp
        apply sum_le_sum
        intro q hq
        split_ifs
        · have h := (Nat.cast_le (α := ℝ)).mpr (consecutive_divisibility_count_le' N p q)
          have hdiv := Nat.cast_div_le (m := N) (n := p*q) (α := ℝ)
          push_cast at h hdiv
          convert h.trans (add_le_add hdiv le_rfl) using 1 <;> ring
        · simp
      _ = _ := by
        simp only [sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,comparablePrimeMass]
        ring
  exact (hcount.trans hsum).trans (add_le_add le_rfl
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast primesAbovePower_card_le A D) 2))

def smallPrimeRatioEvent (C : ℕ) (α : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ (Nat.maxPrimeFac n : ℝ) ≤ (n : ℝ)^α ∧
    (Nat.maxPrimeFac (n+1) : ℝ) ≤ (n : ℝ)^α ∧ factorRatioEvent C n

noncomputable instance (C : ℕ) (α : ℝ) (n : ℕ) : Decidable (smallPrimeRatioEvent C α n) :=
  Classical.propDecidable _

lemma smallPrimeRatioEvent_card_bound (N C A : ℕ) (α : ℝ) (hα0 : 0 ≤ α) :
    (((range N).filter (smallPrimeRatioEvent C α)).card : ℝ) ≤
      (((range N).filter fun n => Nat.maxPrimeFac n ≤ (C+1)*2^A).card : ℝ) +
      N*comparablePrimeMass C A ⌊(N : ℝ)^α⌋₊ + (⌊(N : ℝ)^α⌋₊ : ℝ)^2 := by
  classical
  let D := ⌊(N : ℝ)^α⌋₊
  have hs : (range N).filter (smallPrimeRatioEvent C α) ⊆
      (range N).filter (fun n => Nat.maxPrimeFac n ≤ (C+1)*2^A) ∪ smallPrimeRatioSet N C A D := by
    intro n hn
    obtain ⟨hnN,hn,hp,hq,hcomp⟩ := mem_filter.mp hn
    by_cases hsmall : Nat.maxPrimeFac n ≤ (C+1)*2^A
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,hsmall⟩)
    · apply mem_union_right
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg n)
        (show (n : ℝ) ≤ N by exact_mod_cast (mem_range.mp hnN).le) hα0
      have hpA : 2^A ≤ Nat.maxPrimeFac n := by nlinarith
      have hqA : 2^A ≤ Nat.maxPrimeFac (n+1) := by
        have hcomp' := hcomp.1
        by_contra hqA
        have h := Nat.mul_le_mul_left C (show Nat.maxPrimeFac (n+1) ≤ 2^A by omega)
        nlinarith
      exact mem_filter.mpr ⟨hnN,hn,
        mem_primesAbovePower.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,hpA,Nat.le_floor (hp.trans hpow)⟩,
        mem_primesAbovePower.mpr ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),hqA,Nat.le_floor (hq.trans hpow)⟩,
        hcomp⟩
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hs).trans (card_union_le _ _))
  push_cast at hc
  have h := smallPrimeRatioSet_card_le N C A D
  linarith

lemma floor_rpow_sq_div_tendsto_zero (α : ℝ) (hα : α < 1/2) :
    Tendsto (fun N : ℕ => (⌊(N : ℝ)^α⌋₊ : ℝ)^2/N) atTop (nhds 0) := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < 1-2*α by linarith)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := Nat.floor_le (Real.rpow_nonneg hN0.le α)
  have hs := div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) ⌊(N : ℝ)^α⌋₊) hf 2) hN0.le
  convert hs using 1
  dsimp only [Function.comp_def]
  rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
  have he : -(1-2*α) = α*2-1 := by ring
  rw [he,Real.rpow_sub hN0,Real.rpow_one]
  norm_num

/-- Fixed-ratio near ties have density zero when both largest prime factors
are below any fixed power strictly smaller than the square root. -/
theorem smallPrimeRatioEvent_hasDensity_zero (C : ℕ) (α : ℝ) (hα0 : 0 ≤ α) (hα : α < 1/2) :
    {n | smallPrimeRatioEvent C α n}.HasDensity 0 := by
  classical
  let L := Nat.log 2 C+1
  have hC : C ≤ 2^L := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) C).le
  let f (N : ℕ) : ℝ := (((range N).filter (smallPrimeRatioEvent C α)).card : ℝ)/N
  let e (R N : ℕ) : ℝ :=
    (((range N).filter fun n => Nat.maxPrimeFac n ≤ (C+1)*2^(R+1)).card : ℝ)/N +
      (⌊(N : ℝ)^α⌋₊ : ℝ)^2/N
  have he (R : ℕ) : Tendsto (e R) atTop (nhds 0) := by
    have h1 := (density_iff_count _ 0).mp (bounded_maxPrimeFac_hasDensity_zero ((C+1)*2^(R+1)))
    simpa only [e,add_zero] using h1.add (floor_rpow_sq_div_tendsto_zero α hα)
  have hbound (R N : ℕ) (hN : 0 < N) : f N ≤ e R N + 64*(L+1 : ℝ)/(R+1 : ℝ) := by
    have h := smallPrimeRatioEvent_card_bound N C (R+1) α hα0
    have hmass := comparablePrimeMass_bound C L (R+1) ⌊(N : ℝ)^α⌋₊ hC (by omega)
    have h' := h.trans (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N))) le_rfl)
    have hd := div_le_div_of_nonneg_right h' (Nat.cast_nonneg N)
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    convert hd using 1
    dsimp only [e]
    push_cast
    field_simp
    <;> ring
  have hRlim : Tendsto (fun R : ℕ => 64*(L+1 : ℝ)/(R+1 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (64*(L+1 : ℝ))).comp (tendsto_add_atTop_nat 1)
  rw [density_iff_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨R,hR⟩ := (hRlim.eventually (gt_mem_nhds (half_pos hε))).exists
  filter_upwards [(he R).eventually (gt_mem_nhds (half_pos hε)),eventually_gt_atTop (0 : ℕ)] with N heN hN
  change dist (f N) 0 < ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (show 0 ≤ f N by dsimp [f]; positivity)]
  have hb := hbound R N hN
  linarith

#print axioms smallPrimeRatioEvent_hasDensity_zero
end FiniteSieve
end Erdos371
