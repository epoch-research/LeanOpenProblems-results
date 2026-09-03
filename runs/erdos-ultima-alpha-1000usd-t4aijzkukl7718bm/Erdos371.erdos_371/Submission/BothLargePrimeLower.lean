import Submission.TwoBandLargePrimeLower
import Submission.PositiveComparison
import Submission.PrimeWinnerFlux

/-! A positive lower proportion of consecutive pairs with both largest
prime factors above N^(21/40), obtained by a two-band marginal estimate. -/
namespace Erdos371
open Finset Filter FiniteSieve
open scoped Topology

lemma largePrimeDivisorSet_eq_maxPrimeFac_filter (B N : ℕ) (hB : 1 ≤ B) :
    largePrimeDivisorSet B N=(range N).filter (fun n => B<Nat.maxPrimeFac (n+1)) := by
  classical
  ext n
  simp only [largePrimeDivisorSet,mem_filter]
  apply and_congr_right
  intro hn
  constructor
  · rintro ⟨p,hp,hpd⟩
    obtain ⟨hp,hpB⟩ := mem_filter.mp hp
    have hprime := (Nat.mem_primesBelow.mp hp).2
    exact hpB.trans_le (Nat.le_maxPrimeFac (by omega) hprime hpd)
  · intro hh
    have hn2 : 1<n+1 := (Nat.one_lt_maxPrimeFac_iff (n+1)).mp (by omega)
    refine ⟨Nat.maxPrimeFac (n+1),mem_filter.mpr ⟨?_,hh⟩,Nat.maxPrimeFac_dvd⟩
    exact Nat.mem_primesBelow.mpr ⟨by have := Nat.maxPrimeFac_le (n := n+1); have := mem_range.mp hn; omega,
      Nat.prime_maxPrimeFac_of_one_lt (n+1) hn2⟩

lemma twice_largePrimeDivisor_count_le_both_add_endpoint (B N : ℕ) (hB : 1 ≤ B) :
    2*(largePrimeDivisorSet B N).card ≤ (bothAboveSet B N).card+N+1 := by
  classical
  let A := (range N).filter fun n => B<Nat.maxPrimeFac n
  let C := (range N).filter fun n => B<Nat.maxPrimeFac (n+1)
  have hshift : C.card ≤ A.card+1 := filter_count_shifted_le_add_one (fun n => B<Nat.maxPrimeFac n) N
  have hi : A ∩ C=bothAboveSet B N := by ext n; simp [A,C,bothAboveSet,and_assoc,and_left_comm]
  have hu : (A ∪ C).card ≤ N := by
    exact (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq (card_range N)
  have he := card_union_add_card_inter A C
  rw [hi] at he
  rw [largePrimeDivisorSet_eq_maxPrimeFac_filter B N hB]
  change 2*C.card ≤ _
  omega

/-- A concrete positive lower proportion strictly above the square-root
prime threshold. This says nothing about which comparison orientation wins. -/
theorem bothAbove_upperHalf_positive_proportion :
    ∀ᶠ N : ℕ in atTop, (1/20 : ℝ) ≤
      ((bothAboveSet (ceilPowerCutoff (21/40) N) N).card : ℝ)/N := by
  have hhigh := largePrimeDivisorSet_two_power_bands_eventually_ge (21/40) (3/4)
    (by norm_num) (by norm_num) (by norm_num) (1/100) (by norm_num)
  norm_num only at hhigh
  have hone := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (by norm_num : (0 : ℝ)<1/100)
  filter_upwards [hhigh,hone,eventually_gt_atTop (1 : ℕ)] with N hh ho hN
  have hB := (ceilPowerCutoff_data (21/40) (3/4) (by norm_num) (by norm_num) (by norm_num) N hN).1
  have hc := twice_largePrimeDivisor_count_le_both_add_endpoint (ceilPowerCutoff (21/40) N) N hB.le
  have hc' : (2 : ℝ)*(largePrimeDivisorSet (ceilPowerCutoff (21/40) N) N).card ≤
      (bothAboveSet (ceilPowerCutoff (21/40) N) N).card+N+1 := by exact_mod_cast hc
  have hN0 : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hr := div_le_div_of_nonneg_right hc' hN0.le
  rw [add_div,add_div,div_self hN0.ne',mul_div_assoc] at hr
  linarith

lemma ceilPowerCutoff_upperHalf_product_eventually :
    ∀ᶠ N : ℕ in atTop, 2*N ≤ (ceilPowerCutoff (21/40) N+1)^2 := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/20)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [ht,eventually_gt_atTop (0 : ℕ)] with N hpow hN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hB := Nat.le_ceil ((N : ℝ)^(21/40 : ℝ))
  have hbound : (2 : ℝ)*N ≤ (ceilPowerCutoff (21/40) N+1 : ℝ)^2 := by
    calc
      _ ≤ (N : ℝ)^(1/20 : ℝ)*N := mul_le_mul_of_nonneg_right hpow hN0.le
      _ = (N : ℝ)^(1/20 : ℝ)*(N : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ)^(21/20 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num
      _ = ((N : ℝ)^(21/40 : ℝ))^2 := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
        norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) (hB.trans (by
        change (ceilPowerCutoff (21/40) N : ℝ) ≤ _
        linarith)) 2
  exact_mod_cast hbound

#print axioms bothAbove_upperHalf_positive_proportion
#print axioms ceilPowerCutoff_upperHalf_product_eventually
end Erdos371
