import Submission.PrimeWinnerLogPowerCofactor
import Submission.NarrowPrimeBands

/-! Almost all primes in a dyadic band have zero winner current at every
whole-multiple endpoint in a fixed cofactor range. This does not control
cofactors growing like a positive power of the prime. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

noncomputable def badCofactorPrimes (K X : ℕ) : Finset ℕ :=
  (narrowPrimeBand 1 2 X).filter fun p =>
    ∃ J ≤ K, primeWinnerSum p (J*p+1) ≠ 0

lemma primeWinnerSum_whole_endpoint_eq_loser (p J : ℕ) (hp : p.Prime) :
    primeWinnerSum p (J*p+1) = primeLoserSum p (J*p+1) := by
  have hn : Nat.maxPrimeFac (J*p+1) ≠ p := by
    intro he
    have hd : p ∣ J*p+1 := by
      have hd : Nat.maxPrimeFac (J*p+1) ∣ J*p+1 := Nat.maxPrimeFac_dvd
      rwa [he] at hd
    have hd' : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_mul_left p J)).mpr hd
    exact hp.not_dvd_one hd'
  have hz : Nat.maxPrimeFac 0 ≠ p := by simpa using hp.ne_zero.symm
  have h := primeWinnerSum_sub_primeLoserSum p (J*p+1)
  simp only [if_neg hn,if_neg hz,sub_self] at h
  exact sub_eq_zero.mp h

lemma badCofactorPrimes_subset_loser_image (K X : ℕ) (hX : 0 < X) :
    badCofactorPrimes K X ⊆
      (bothAboveSet X ((2*K+1)*X)).image primeLoser := by
  intro p hp
  obtain ⟨hpband,J,hJK,hJ⟩ := mem_filter.mp hp
  have hpprime : p.Prime := (mem_filter.mp (mem_sdiff.mp hpband).1).2
  obtain ⟨hpX,hpupper⟩ := narrowPrimeBand_member_bounds 1 2 X p hpband
  simp only [one_mul] at hpX
  have hpX' : X < p := by exact_mod_cast hpX
  have hpupper' : p ≤ 2*X := by
    change p ≤ ⌊(2 : ℝ)*(X : ℝ)⌋₊ at hpupper
    rw [show (2 : ℝ)*X = ((2*X : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast] at hpupper
    exact hpupper
  rw [primeWinnerSum_whole_endpoint_eq_loser p J hpprime] at hJ
  unfold primeLoserSum at hJ
  obtain ⟨n,hn,_⟩ := exists_ne_zero_of_sum_ne_zero hJ
  obtain ⟨hnrange,hnloser⟩ := mem_filter.mp hn
  apply mem_image.mpr
  refine ⟨n,mem_filter.mpr ⟨mem_range.mpr ?_,?_⟩,hnloser⟩
  · have hn' := mem_range.mp hnrange
    have hprod := Nat.mul_le_mul hJK hpupper'
    nlinarith
  · have h := hpX'
    rw [← hnloser,primeLoser,lt_min_iff] at h
    exact h

lemma badCofactorPrimes_card_le (K X : ℕ) (hX : 0 < X) :
    (badCofactorPrimes K X).card ≤ (bothAboveSet X ((2*K+1)*X)).card :=
  (card_le_card (badCofactorPrimes_subset_loser_image K X hX)).trans card_image_le

/-- Uniform finite estimate; the integer multiplier need not be fixed. -/
lemma bothAbove_linear_scaled_log_bound (c X : ℕ) (hc : 0 < c) (hX : 2 ≤ X)
    (huX : Real.log c/Real.log (c*X : ℕ) ≤ 1/8) :
    ((bothAboveSet X (c*X)).card : ℝ)*Real.log X/X ≤
      largePairConstant*c*(Real.log c+1)^2/Real.log X +
        (2 : ℝ)^65*c*Real.log X/(X : ℝ)^(1/2 : ℝ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast hX
  have hXN : X ≤ c*X := by nlinarith
  have hN : 1 < c*X := by omega
  have hN0 : (0 : ℝ) < (c*X : ℕ) := by exact_mod_cast (show 0 < c*X by omega)
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have hlN : 0 < Real.log (c*X : ℕ) := Real.log_pos (by exact_mod_cast hN)
  have hlXN : Real.log X ≤ Real.log (c*X : ℕ) :=
    Real.log_le_log hX0 (by exact_mod_cast hXN)
  let u := Real.log c/Real.log (c*X : ℕ)
  have hu0 : 0 ≤ u := div_nonneg (Real.log_nonneg hc1) hlN.le
  have hpow : ((c*X : ℕ) : ℝ)^u = c := by
    rw [Real.rpow_def_of_pos hN0]
    dsimp only [u]
    rw [mul_div_cancel₀ _ hlN.ne',Real.exp_log hcR]
  have hcut : ((c*X : ℕ) : ℝ)^(1-u) = X := by
    rw [Real.rpow_sub hN0,Real.rpow_one,hpow,Nat.cast_mul]
    exact mul_div_cancel_left₀ _ hcR.ne'
  have hsub : bothAboveSet X (c*X) ⊆ bothLargePrimeSet (c*X) u := by
    intro n hn
    obtain ⟨hnN,hn,hn'⟩ := mem_filter.mp hn
    apply mem_filter.mpr
    refine ⟨hnN,?_,?_⟩ <;> rw [hcut] <;> exact_mod_cast ‹_›
  have hcard := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)) hN0.le
  have hb := hcard.trans (bothLargePrimeSet_ratio_bound (c*X) u hN hu0 huX)
  have hb' := mul_le_mul_of_nonneg_right hb (mul_nonneg hcR.le hlX.le)
  have hleft : ((bothAboveSet X (c*X)).card : ℝ)/(c*X : ℕ)*
      ((c : ℝ)*Real.log X) = ((bothAboveSet X (c*X)).card : ℝ)*Real.log X/X := by
    push_cast
    field_simp
  rw [hleft] at hb'
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hfrac : u+1/Real.log (c*X : ℕ) ≤ (Real.log c+1)/Real.log X := by
    calc
      _ = (Real.log c+1)/Real.log (c*X : ℕ) := by dsimp only [u]; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hlX hlXN
  have hmainle : largePairConstant*(u+1/Real.log (c*X : ℕ))^2*
      ((c : ℝ)*Real.log X) ≤ largePairConstant*c*(Real.log c+1)^2/Real.log X := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ u+1/Real.log (c*X : ℕ)) hfrac 2
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC)
      (mul_nonneg hcR.le hlX.le)
    convert hm using 1
    field_simp
  have hpowle : ((c*X : ℕ) : ℝ)^(-1/2 : ℝ) ≤ 1/(X : ℝ)^(1/2 : ℝ) := by
    rw [show (-1/2 : ℝ) = -(1/2) by ring,Real.rpow_neg hN0.le,← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hX0 _)
      (Real.rpow_le_rpow hX0.le (by exact_mod_cast hXN) (by norm_num))
  have herrle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpowle (show 0 ≤ (2 : ℝ)^65 by positivity))
    (mul_nonneg hcR.le hlX.le)
  calc
    _ ≤ _ := hb'
    _ = largePairConstant*(u+1/Real.log (c*X : ℕ))^2*((c : ℝ)*Real.log X) +
        (2 : ℝ)^65*((c*X : ℕ) : ℝ)^(-1/2 : ℝ)*((c : ℝ)*Real.log X) := by ring
    _ ≤ largePairConstant*c*(Real.log c+1)^2/Real.log X +
        (2 : ℝ)^65*c*Real.log X/(X : ℝ)^(1/2 : ℝ) := by
      apply add_le_add hmainle
      simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using herrle

/-- A logarithmically strengthened sparsity estimate for two prime factors
above a fixed fraction of the endpoint. -/
lemma bothAbove_linear_count_scaled_log_tendsto (c : ℕ) (hc : 0 < c) :
    Tendsto (fun X : ℕ => ((bothAboveSet X (c*X)).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hlog : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hclog : Tendsto (fun X : ℕ => Real.log (c*X : ℕ)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    simpa only [Nat.cast_mul] using
      tendsto_natCast_atTop_atTop.const_mul_atTop hcR
  have hu : Tendsto (fun X : ℕ => Real.log c/Real.log (c*X : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hclog
  have hmain : Tendsto (fun X : ℕ =>
      largePairConstant*(c : ℝ)*(Real.log c+1)^2/Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have herr : Tendsto (fun X : ℕ =>
      (2 : ℝ)^65*c*Real.log X/(X : ℝ)^(1/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_div_assoc,mul_zero] using
      (log_nat_rpow_div_rpow_tendsto_zero 1 (1/2) (by norm_num)).const_mul
        ((2 : ℝ)^65*c)
  have ht := hmain.add herr
  simp only [add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ ht
  filter_upwards [eventually_ge_atTop (2 : ℕ),hu.eventually_le_const
    (by norm_num : (0 : ℝ) < 1/8)] with X hX huX
  exact bothAbove_linear_scaled_log_bound c X hc hX huX

/-- Fixed cofactors are harmless for almost every prime, even when every
whole-multiple endpoint in the range must have exactly zero current. -/
theorem badCofactorPrimes_scaled_count_tendsto (K : ℕ) :
    Tendsto (fun X : ℕ => ((badCofactorPrimes K X).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ (bothAbove_linear_count_scaled_log_tendsto (2*K+1) (by omega))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      ((Nat.cast_le (α := ℝ)).mpr (badCofactorPrimes_card_le K X hX))
      (Real.log_natCast_nonneg X)) (Nat.cast_nonneg X)

/-- The exceptional proportion among primes in `(X,2X]` tends to zero.
The cofactor bound is fixed before taking this limit. -/
theorem badCofactorPrimes_prime_proportion_tendsto (K : ℕ) :
    Tendsto (fun X : ℕ => ((badCofactorPrimes K X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  have ht := (badCofactorPrimes_scaled_count_tendsto K).div hden one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hl : Real.log X ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Pi.div_apply]
  field_simp

#print axioms badCofactorPrimes_subset_loser_image
#print axioms bothAbove_linear_count_scaled_log_tendsto
#print axioms badCofactorPrimes_prime_proportion_tendsto
end Erdos371
