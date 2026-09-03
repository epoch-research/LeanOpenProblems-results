import Submission.PrimeSmoothNeighborRuns
import Submission.PrimeWinnerCriticalCofactor

/-! A nearly logarithmic range of simultaneous smooth neighbors for almost
all primes. This still does not control the power-cofactor interior. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

noncomputable def criticalPrimeRunWeight (r : ℝ) (X : ℕ) : ℝ :=
  Real.log X/(1+Real.log (Real.log X))^r

noncomputable def criticalPrimeRunCutoff (r : ℝ) (X : ℕ) : ℕ :=
  ⌊criticalPrimeRunWeight r X⌋₊

lemma criticalPrimeRun_data (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X ∧ 1 ≤ criticalPrimeRunWeight r X ∧
      criticalPrimeRunWeight r X ≤ Real.log X ∧
      0 < criticalPrimeRunCutoff r X ∧ criticalPrimeRunCutoff r X ≤ X := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (one_add_log_rpow_div_rpow_tendsto_zero r 1 hr (by norm_num)).comp hL
  simp only [Real.rpow_one] at ht
  filter_upwards [hL.eventually_ge_atTop 1,ht.eventually_le_const
    (by norm_num : (0 : ℝ) < 1),logPowerCofactorCutoff_eventually_le_endpoint 1]
    with X hL hsmall hlogcut
  have hL0 : 0 < Real.log X := by linarith
  have hB : 1 ≤ 1+Real.log (Real.log X) := by have := Real.log_nonneg hL; linarith
  have hden : 1 ≤ (1+Real.log (Real.log X))^r := Real.one_le_rpow hB hr
  have hden0 : 0 < (1+Real.log (Real.log X))^r := by linarith
  have hdenL : (1+Real.log (Real.log X))^r ≤ Real.log X := by
    simpa only [one_mul] using (div_le_iff₀ hL0).mp hsmall
  have hW1 : 1 ≤ criticalPrimeRunWeight r X := by
    exact (le_div_iff₀ hden0).mpr (by simpa only [one_mul] using hdenL)
  have hWL : criticalPrimeRunWeight r X ≤ Real.log X := by
    apply (div_le_iff₀ hden0).mpr
    nlinarith
  have hK : 0 < criticalPrimeRunCutoff r X := (Nat.one_le_floor_iff _).mpr hW1
  refine ⟨hL,hW1,hWL,hK,?_⟩
  apply le_trans (Nat.floor_mono hWL)
  simpa only [logPowerCofactorCutoff,Real.rpow_one] using hlogcut

lemma criticalPrimeRunWeight_dominates_logPower (r a M : ℝ)
    (hr : 0 ≤ r) (ha : a < 1) :
    ∀ᶠ X : ℕ in atTop, M*(Real.log X)^a ≤ criticalPrimeRunWeight r X := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := ((one_add_log_rpow_div_rpow_tendsto_zero r (1-a) hr
    (by linarith)).comp hL).const_mul M
  simp only [mul_zero] at ht
  filter_upwards [ht.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hL.eventually_ge_atTop 1] with X hsmall hLN
  have hL0 : 0 < Real.log X := by linarith
  have hB0 : 0 < 1+Real.log (Real.log X) := by have := Real.log_nonneg hLN; positivity
  have hden0 := Real.rpow_pos_of_pos hB0 r
  have hpow0 := Real.rpow_pos_of_pos hL0 (1-a)
  have hh : M*(1+Real.log (Real.log X))^r ≤ (Real.log X)^(1-a) := by
    have hh' : (M*(1+Real.log (Real.log X))^r)/(Real.log X)^(1-a) ≤ 1 := by
      simpa only [mul_div_assoc,Function.comp_apply] using hsmall
    simpa only [one_mul] using (div_le_iff₀ hpow0).mp hh'
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hL0.le a)
  rw [← Real.rpow_add hL0,sub_add_cancel,Real.rpow_one] at hm
  unfold criticalPrimeRunWeight
  apply (le_div_iff₀ hden0).mpr
  nlinarith

lemma criticalPrimeRunCutoff_tendsto_atTop (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (criticalPrimeRunCutoff r) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [criticalPrimeRunWeight_dominates_logPower r (1/2) 1 hr (by norm_num),
    (logPowerCofactorCutoff_tendsto_atTop (1/2) (by norm_num)).eventually_ge_atTop B]
    with X hdom hB
  apply hB.trans
  apply Nat.floor_mono
  simpa only [one_mul] using hdom

lemma criticalPrimeRun_bothAbove_eventual_bound (r : ℝ) (hr : 0 ≤ r) :
    ∀ᶠ X : ℕ in atTop,
      ((bothAboveSet X ((2*criticalPrimeRunCutoff r X+1)*X)).card : ℝ)*Real.log X/X ≤
        (4*largePairConstant*(2*Real.log 2+1)^2)/(1+Real.log (Real.log X))^(r-2) +
          (4*(2 : ℝ)^65)*(Real.log X)^2/(X : ℝ)^(1/2 : ℝ) := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu1 : Tendsto (fun X : ℕ => Real.log 4/Real.log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  have hu2 : Tendsto (fun X : ℕ => Real.log (Real.log X)/Real.log X) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hL
  have hu := hu1.add hu2
  simp only [add_zero] at hu
  filter_upwards [criticalPrimeRun_data r hr,hu.eventually_le_const
    (by norm_num : (0 : ℝ) < 1/8),eventually_ge_atTop (2 : ℕ)] with X hd huX hX
  obtain ⟨hLN,hW1,hWL,_,_⟩ := hd
  let K := criticalPrimeRunCutoff r X
  let c := 2*K+1
  let W := criticalPrimeRunWeight r X
  let B : ℝ := 1+Real.log (Real.log X)
  let D : ℝ := 2*Real.log 2+1
  have hc : 0 < c := by dsimp [c]; omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hLL : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hLN
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hB0 : 0 < B := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKW : (K : ℝ) ≤ W := Nat.floor_le (by linarith)
  have hcW : (c : ℝ) ≤ 4*W := by dsimp [c]; push_cast; linarith
  have hcL : (c : ℝ) ≤ 4*Real.log X := hcW.trans (by linarith)
  have hlog4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogc : Real.log c ≤ Real.log 4+Real.log (Real.log X) := by
    have hh := Real.log_le_log hcR hcL
    rwa [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hL0.ne'] at hh
  have hlogc1 : Real.log c+1 ≤ D*B := by
    rw [hlog4] at hlogc
    dsimp [D,B]
    nlinarith [mul_nonneg h2 hLL]
  have hXN : X ≤ c*X := by nlinarith
  have hlogXN := Real.log_le_log hX0 (by exact_mod_cast hXN : (X : ℝ) ≤ (c*X : ℕ))
  have hcu : Real.log c/Real.log (c*X : ℕ) ≤ 1/8 := by
    calc
      _ ≤ Real.log c/Real.log X :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg c) hL0 hlogXN
      _ ≤ (Real.log 4+Real.log (Real.log X))/Real.log X :=
        div_le_div_of_nonneg_right hlogc hL0.le
      _ ≤ 1/8 := by simpa only [add_div] using huX
  have hC : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  have hmain : largePairConstant*c*(Real.log c+1)^2/Real.log X ≤
      4*largePairConstant*D^2/B^(r-2) := by
    have hsq := pow_le_pow_left₀ (by have := Real.log_natCast_nonneg c; positivity :
      0 ≤ Real.log c+1) hlogc1 2
    have hprod := mul_le_mul hcW hsq (sq_nonneg (Real.log c+1)) (by linarith : 0 ≤ 4*W)
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hprod hC) hL0.le
    apply (show largePairConstant*c*(Real.log c+1)^2/Real.log X ≤
      largePairConstant*(4*W)*(D*B)^2/Real.log X by
        simpa only [mul_assoc] using hm).trans_eq
    rw [Real.rpow_sub hB0,Real.rpow_two]
    dsimp only [W,criticalPrimeRunWeight,B]
    field_simp
  have herr : (2 : ℝ)^65*c*Real.log X/(X : ℝ)^(1/2 : ℝ) ≤
      (4*(2 : ℝ)^65)*(Real.log X)^2/(X : ℝ)^(1/2 : ℝ) := by
    have hm := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcL (show 0 ≤ (2 : ℝ)^65 by positivity)) hL0.le)
      (Real.rpow_nonneg hX0.le (1/2 : ℝ))
    convert hm using 1
    ring
  exact (bothAbove_linear_scaled_log_bound c X hc hX hcu).trans (add_le_add hmain herr)

lemma criticalPrimeRun_bothAbove_scaled_count_tendsto (r : ℝ) (hr : 2 < r) :
    Tendsto (fun X : ℕ =>
      ((bothAboveSet X ((2*criticalPrimeRunCutoff r X+1)*X)).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun X : ℕ => 1+Real.log (Real.log X)) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp hL)
  have hmain : Tendsto (fun X : ℕ =>
      (4*largePairConstant*(2*Real.log 2+1)^2)/(1+Real.log (Real.log X))^(r-2))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (by linarith : 0 < r-2)).comp hB)
  have herr := (log_nat_pow_div_rpow_tendsto_zero 2 (1/2)
    (by norm_num)).const_mul (4*(2 : ℝ)^65)
  have ht := hmain.add herr
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ ht
  simpa only [mul_div_assoc] using criticalPrimeRun_bothAbove_eventual_bound r (by linarith)

theorem criticalPrimeRun_roughNeighborPrimes_scaled_count_tendsto (r : ℝ) (hr : 2 < r) :
    Tendsto (fun X : ℕ =>
      ((roughNeighborPrimes (criticalPrimeRunCutoff r X) X).card : ℝ)*Real.log X/X)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun X => by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg X))
      (Nat.cast_nonneg X))) _ (criticalPrimeRun_bothAbove_scaled_count_tendsto r hr)
  filter_upwards [criticalPrimeRun_data r (by linarith),eventually_gt_atTop (0 : ℕ)] with X hd hX
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (roughNeighborPrimes_card_le _ X hX hd.2.2.2.2))
    (Real.log_natCast_nonneg X)) (Nat.cast_nonneg X)

theorem criticalPrimeRun_roughNeighborPrimes_proportion_tendsto (r : ℝ) (hr : 2 < r) :
    Tendsto (fun X : ℕ => ((roughNeighborPrimes (criticalPrimeRunCutoff r X) X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  have ht := (criticalPrimeRun_roughNeighborPrimes_scaled_count_tendsto r hr).div hden one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with X hX
  have hx : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hl : Real.log X ≠ 0 := (Real.log_pos (by exact_mod_cast hX)).ne'
  simp only [Pi.div_apply]
  field_simp

lemma criticalPrimeRunCutoff_dyadic_domination (r s : ℝ) (hs : 0 ≤ s) (hsr : s < r) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, X < p → p ≤ 2*X →
      criticalPrimeRunCutoff r p ≤ criticalPrimeRunCutoff s X := by
  have hL : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun X : ℕ => 1+Real.log (Real.log X)) atTop atTop :=
    tendsto_const_nhds.add_atTop (Real.tendsto_log_atTop.comp hL)
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hsr)).comp hB
  filter_upwards [hL.eventually_ge_atTop 1,ht.eventually_ge_atTop 2,
    eventually_ge_atTop (2 : ℕ)] with X hLN hpow hX
  intro p hpX hp2X
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL0 : 0 < Real.log X := by linarith
  have hLX : Real.log X ≤ Real.log p := Real.log_le_log hX0 (by exact_mod_cast hpX.le)
  have hlogp : Real.log p ≤ 2*Real.log X := by
    have h := Real.log_le_log hp0 (by exact_mod_cast hp2X : (p : ℝ) ≤ 2*X)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hX : (2 : ℝ) ≤ X)
    linarith
  let B : ℝ := 1+Real.log (Real.log X)
  have hB0 : 0 < B := by dsimp [B]; have := Real.log_nonneg hLN; positivity
  have hBB : B ≤ 1+Real.log (Real.log p) := by
    dsimp only [B]
    exact add_le_add_right (Real.log_le_log hL0 hLX) 1
  have hr0 : 0 ≤ r := hs.trans hsr.le
  have hden := Real.rpow_le_rpow hB0.le hBB hr0
  have hdenr := Real.rpow_pos_of_pos hB0 r
  have hdens := Real.rpow_pos_of_pos hB0 s
  have hdenrs : 2*B^s ≤ B^r := by
    change 2 ≤ B^(r-s) at hpow
    have hh := mul_le_mul_of_nonneg_right hpow hdens.le
    rw [← Real.rpow_add hB0,sub_add_cancel] at hh
    exact hh
  unfold criticalPrimeRunCutoff
  apply Nat.floor_mono
  unfold criticalPrimeRunWeight
  calc
    _ ≤ Real.log p/B^r := div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) hdenr hden
    _ ≤ (2*Real.log X)/B^r := div_le_div_of_nonneg_right hlogp hdenr.le
    _ ≤ Real.log X/B^s := (div_le_div_iff₀ hdenr hdens).mpr (by nlinarith)

noncomputable def criticalRoughNeighborPrimesAtOwnScale (r : ℝ) (X : ℕ) : Finset ℕ :=
  (narrowPrimeBand 1 2 X).filter fun p => ∃ k ≤ criticalPrimeRunCutoff r p, 1 ≤ k ∧
    (p < Nat.maxPrimeFac (k*p-1) ∨ p < Nat.maxPrimeFac (k*p+1))

/-- Nearly logarithmic smooth-neighbor runs for almost every dyadic-band
prime, with the range measured at the prime itself. -/
theorem criticalRoughNeighborPrimesAtOwnScale_proportion_tendsto (r : ℝ) (hr : 2 < r) :
    Tendsto (fun X : ℕ => ((criticalRoughNeighborPrimesAtOwnScale r X).card : ℝ)/
      (narrowPrimeBand 1 2 X).card) atTop (𝓝 0) := by
  let s : ℝ := (r+2)/2
  have hs : 2 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _
    (criticalPrimeRun_roughNeighborPrimes_proportion_tendsto s hs)
  filter_upwards [criticalPrimeRunCutoff_dyadic_domination r s (by linarith) hsr] with X hdom
  have hsub : criticalRoughNeighborPrimesAtOwnScale r X ⊆
      roughNeighborPrimes (criticalPrimeRunCutoff s X) X := by
    intro p hp
    obtain ⟨hpband,k,hk,hk1,hrough⟩ := mem_filter.mp hp
    obtain ⟨_,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
    exact mem_filter.mpr ⟨hpband,k,hk.trans (hdom p hpX hp2X),hk1,hrough⟩
  exact div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub))
    (Nat.cast_nonneg _)

/-- An unconditional infinitude statement for this nearly logarithmic run
length. It is not a density result for all consecutive integers. -/
theorem infinitely_many_critical_prime_smooth_neighbor_runs (r : ℝ) (hr : 2 < r) :
    {p : ℕ | p.Prime ∧ ∀ k ∈ Icc 1 (criticalPrimeRunCutoff r p),
      Nat.maxPrimeFac (k*p-1) < p ∧ Nat.maxPrimeFac (k*p+1) < p}.Infinite := by
  let s : ℝ := (r+2)/2
  have hs : 2 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hden := narrowPrimeBand_card_scaled_limit 1 2 (by norm_num) (by norm_num)
  norm_num only at hden
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨X,hd,hdom,hbad,hband,hM⟩ := ((criticalPrimeRun_data s (by linarith)).and
    ((criticalPrimeRunCutoff_dyadic_domination r s (by linarith) hsr).and
    (((criticalPrimeRun_roughNeighborPrimes_scaled_count_tendsto s hs).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1/4)).and
    ((hden.eventually_const_lt (by norm_num : (1/2 : ℝ) < 1)).and
      (eventually_ge_atTop M))))).exists
  have hlt : (roughNeighborPrimes (criticalPrimeRunCutoff s X) X).card <
      (narrowPrimeBand 1 2 X).card := by
    by_contra h
    have hle : ((narrowPrimeBand 1 2 X).card : ℝ) ≤
        (roughNeighborPrimes (criticalPrimeRunCutoff s X) X).card := by exact_mod_cast (not_lt.mp h)
    have hle' := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hle (Real.log_natCast_nonneg X)) (Nat.cast_nonneg (α := ℝ) X)
    linarith
  have hnot : ¬narrowPrimeBand 1 2 X ⊆ roughNeighborPrimes (criticalPrimeRunCutoff s X) X := by
    intro h
    exact (not_le_of_gt hlt) (card_le_card h)
  obtain ⟨p,hp⟩ := sdiff_nonempty.mpr hnot
  obtain ⟨hpband,hpnot⟩ := mem_sdiff.mp hp
  obtain ⟨hprime,hpX,hp2X⟩ := dyadicPrimeBand_nat_data hpband
  refine ⟨p,⟨hprime,?_⟩,by omega⟩
  intro k hk
  have hrun := smooth_neighbors_of_not_mem_roughNeighborPrimes
    (criticalPrimeRunCutoff s X) X p hd.2.2.2.2 hpband hpnot
  obtain ⟨hk1,hkK⟩ := mem_Icc.mp hk
  exact hrun k (mem_Icc.mpr ⟨hk1,hkK.trans (hdom p hpX hp2X)⟩)

#print axioms criticalPrimeRunWeight_dominates_logPower
#print axioms criticalPrimeRun_bothAbove_eventual_bound
#print axioms criticalPrimeRun_roughNeighborPrimes_proportion_tendsto
#print axioms criticalRoughNeighborPrimesAtOwnScale_proportion_tendsto
#print axioms infinitely_many_critical_prime_smooth_neighbor_runs
end Erdos371
