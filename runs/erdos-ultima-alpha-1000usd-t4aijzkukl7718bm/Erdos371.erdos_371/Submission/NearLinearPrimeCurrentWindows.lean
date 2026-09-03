import Submission.PrimeHarmonicDivergenceConvergence
import Submission.PrimeWinnerGrowingCofactor

/-! Absolute harmonic-current cancellation in bounded-ratio windows for every
near-linear prime cutoff. The fixed-power interior is not estimated. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma primeHarmonicFluxError_finset_bound (M : ℕ) (P : Finset ℕ) :
    (∑ p ∈ P, ‖primeHarmonicFluxError M p‖) ≤ 2/(M+1 : ℝ) :=
  ((primeHarmonicFluxError_summable M).norm.sum_le_tsum P
    (fun _ _ => norm_nonneg _)).trans (primeHarmonicFluxError_l1_bound M)

lemma primeHarmonicWindow_flux_bound (P : Finset ℕ) (L U : ℕ)
    (hL : 2≤L) (hU : 2≤U) :
    (∑ p ∈ P, ‖(rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L)-
      (rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L)‖) ≤
        2/(U-1 : ℝ)+2/(L-1 : ℝ) := by
  have he (p : ℕ) :
      (rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L)-
        (rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L) =
      primeHarmonicFluxError (U-2) p-primeHarmonicFluxError (L-2) p := by
    simp only [primeHarmonicFluxError,Nat.sub_add_cancel hL,Nat.sub_add_cancel hU]
    ring
  simp_rw [he]
  calc
    _ ≤ ∑ p ∈ P, (‖primeHarmonicFluxError (U-2) p‖+
        ‖primeHarmonicFluxError (L-2) p‖) := sum_le_sum fun p _ => norm_sub_le _ _
    _ ≤ 2/((U-2 : ℕ)+1 : ℝ)+2/((L-2 : ℕ)+1 : ℝ) := by
      rw [sum_add_distrib]
      exact add_le_add (primeHarmonicFluxError_finset_bound (U-2) P)
        (primeHarmonicFluxError_finset_bound (L-2) P)
    _ = _ := by rw [Nat.cast_sub hL,Nat.cast_sub hU]; push_cast; ring

lemma primeLoserHarmonicWindow_high_bound (P : Finset ℕ) (B L U : ℕ)
    (hP : ∀ p ∈ P, B<p) (hL : 0<L) (hLU : L≤U) :
    (∑ p ∈ P, ‖rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L‖) ≤
      (bothAboveSet B U).card/(L : ℝ) := by
  classical
  have hp (p : ℕ) : ‖rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L‖ ≤
      ∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), (1 : ℝ)/n := by
    change ‖(∑ n ∈ range U, primeLoserHarmonicTerm p n)-
      ∑ n ∈ range L, primeLoserHarmonicTerm p n‖ ≤ _
    rw [← sum_Ico_eq_sub _ hLU]
    have hn := norm_sum_le (Ico L U) (primeLoserHarmonicTerm p)
    simpa only [primeLoserHarmonicTerm,sum_filter,apply_ite,norm_zero,
      norm_div,factorSign_norm,Real.norm_natCast] using hn
  let T := (Ico L U).filter (fun n => primeLoser n∈P)
  have hT : T⊆bothAboveSet B U := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    have hb := hP _ hp
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (mem_Ico.mp hn).2,?_⟩
    simpa only [primeLoser,lt_min_iff] using hb
  calc
    _ ≤ ∑ p ∈ P, ∑ n ∈ (Ico L U).filter (fun n => primeLoser n=p), (1 : ℝ)/n :=
      sum_le_sum fun p _ => hp p
    _ = ∑ n ∈ T, (1 : ℝ)/n := sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ _n ∈ T, (1 : ℝ)/L := by
      apply sum_le_sum
      intro n hn
      apply one_div_le_one_div_of_le (by exact_mod_cast hL)
      exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
    _ = (T.card : ℝ)/L := by simp only [sum_const,nsmul_eq_mul,mul_one_div]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hT) (Nat.cast_nonneg L)

/-- The estimate is uniform in the chosen finite set of high prime labels.
Only the simultaneous-large-prime count and a reciprocal endpoint error remain. -/
theorem primeWinnerHarmonicWindow_high_bound (P : Finset ℕ) (B L U : ℕ)
    (hP : ∀ p ∈ P, B<p) (hL : 2≤L) (hLU : L≤U) :
    (∑ p ∈ P, ‖rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L‖) ≤
      (bothAboveSet B U).card/(L : ℝ)+2/(U-1 : ℝ)+2/(L-1 : ℝ) := by
  have h (p : ℕ) := norm_sub_le_norm_sub_add_norm_sub
    (rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L)
    (rawPrimeLoserHarmonic p U-rawPrimeLoserHarmonic p L) 0
  simp only [sub_zero] at h
  have hs := sum_le_sum (s := P) (fun p _ => h p)
  rw [sum_add_distrib] at hs
  have hf := primeHarmonicWindow_flux_bound P L U hL (hL.trans hLU)
  have hl := primeLoserHarmonicWindow_high_bound P B L U hP (by omega) hLU
  linarith

/-- Any cutoff that eventually exceeds every fixed power U^(1-u), u>0,
makes the simultaneous-high event negligible. No rate of approach is required. -/
theorem bothAbove_nearlinear_ratio_zero (B U : ℕ → ℕ)
    (hU : Tendsto U atTop atTop)
    (hcut : ∀ u : ℝ, 0<u → ∀ᶠ N : ℕ in atTop, (U N : ℝ)^(1-u)≤B N) :
    Tendsto (fun N => (bothAboveSet (B N) (U N)).card/(U N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun N => hε.trans_le (by positivity)
  · intro ε hε
    have hC : 0≤FiniteSieve.largePairConstant := by
      unfold FiniteSieve.largePairConstant
      positivity
    let u : ℝ := min (1/8) (ε/(4*(FiniteSieve.largePairConstant+1)))
    have hu0 : 0<u := lt_min (by norm_num) (by positivity)
    have hu : u≤1/8 := min_le_left _ _
    have huε : u*(4*(FiniteSieve.largePairConstant+1))≤ε :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hsq : u^2≤u := by nlinarith
    have hcu : FiniteSieve.largePairConstant*u^2≤ε/4 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq hC]
    have he := hU.eventually (FiniteSieve.bothLargePrimeSet_eventually_ratio_le
      u hu0.le hu (ε/2) (half_pos hε))
    filter_upwards [hcut u hu0,he] with N hcut he
    have hsub : bothAboveSet (B N) (U N)⊆FiniteSieve.bothLargePrimeSet (U N) u := by
      intro n hn
      obtain ⟨hn,hp,hq⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hn,hcut.trans_lt (by exact_mod_cast hp),
        hcut.trans_lt (by exact_mod_cast hq)⟩
    have hc := div_le_div_of_nonneg_right
      (show ((bothAboveSet (B N) (U N)).card : ℝ)≤
        (FiniteSieve.bothLargePrimeSet (U N) u).card by exact_mod_cast card_le_card hsub)
      (Nat.cast_nonneg (α := ℝ) (U N))
    linarith

/-- Absolute current cancellation on every bounded-ratio moving window,
for arbitrary finite sets of labels above a near-linear cutoff. -/
theorem primeWinnerHarmonicWindow_nearlinear_zero (B L U : ℕ → ℕ)
    (P : ℕ → Finset ℕ) (R : ℝ)
    (hL : Tendsto L atTop atTop) (hU : Tendsto U atTop atTop)
    (hdata : ∀ᶠ N : ℕ in atTop, L N≤U N ∧ (U N : ℝ)≤R*L N ∧
      ∀ p ∈ P N, B N<p)
    (hcut : ∀ u : ℝ, 0<u → ∀ᶠ N : ℕ in atTop, (U N : ℝ)^(1-u)≤B N) :
    Tendsto (fun N => ∑ p ∈ P N,
      ‖rawPrimeWinnerHarmonic p (U N)-rawPrimeWinnerHarmonic p (L N)‖)
      atTop (𝓝 0) := by
  have hb := (bothAbove_nearlinear_ratio_zero B U hU hcut).const_mul R
  have hUr : Tendsto (fun N => (U N : ℝ)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_natCast_atTop_atTop.comp hU).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  have hLr : Tendsto (fun N => (L N : ℝ)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_natCast_atTop_atTop.comp hL).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
  have ht := (hb.add ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hUr)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop hLr)
  simp only [mul_zero,add_zero] at ht
  apply squeeze_zero' (Eventually.of_forall fun N => sum_nonneg fun p _ => norm_nonneg _) _ ht
  filter_upwards [hdata,hL.eventually_ge_atTop 2] with N hd hLN
  have hLpos : (0 : ℝ)<L N := by exact_mod_cast (show 0<L N by omega)
  have hUpos : (0 : ℝ)<U N := by exact_mod_cast (show 0<U N by omega)
  have hc : (bothAboveSet (B N) (U N)).card/(L N : ℝ) ≤
      R*((bothAboveSet (B N) (U N)).card/(U N : ℝ)) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hLpos hUpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd.2.1
      (Nat.cast_nonneg (α := ℝ) (bothAboveSet (B N) (U N)).card)]
  exact (primeWinnerHarmonicWindow_high_bound (P N) (B N) (L N) (U N)
    hd.2.2 hLN hd.1).trans (by linarith)

/-- The customary logarithmic-ratio hypothesis supplies the near-linear
power bounds used above. Positivity of the cutoff is retained explicitly. -/
lemma nearlinear_power_bounds_of_log_ratio (B U : ℕ → ℕ)
    (hU : Tendsto U atTop atTop) (hB : ∀ᶠ N : ℕ in atTop, 0<B N)
    (hratio : Tendsto (fun N => Real.log (B N)/Real.log (U N)) atTop (𝓝 1)) :
    ∀ u : ℝ, 0<u → ∀ᶠ N : ℕ in atTop, (U N : ℝ)^(1-u)≤B N := by
  intro u hu
  filter_upwards [hU.eventually_gt_atTop 1,hB,
    hratio.eventually_const_lt (show 1-u<1 by linarith)] with N hUN hBN hr
  have hUpos : (0 : ℝ)<U N := by exact_mod_cast (show 0<U N by omega)
  have hBpos : (0 : ℝ)<B N := by exact_mod_cast hBN
  have hlog : 0<Real.log (U N) := Real.log_pos (by exact_mod_cast hUN)
  have he := Real.exp_le_exp.mpr ((lt_div_iff₀ hlog).mp hr).le
  rw [Real.exp_log hBpos] at he
  rw [Real.rpow_def_of_pos hUpos]
  simpa only [mul_comm] using he

noncomputable def primeHarmonicWindowL1Above (B L U : ℕ) : ℝ :=
  ∑ p ∈ Ioc B (U+1),
    ‖rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L‖

lemma rawPrimeWinnerHarmonic_zero_above_endpoint (p N : ℕ) (hp : N<p) :
    rawPrimeWinnerHarmonic p N=0 := by
  apply sum_eq_zero
  intro n hn
  have hnN := mem_range.mp hn
  have hw : primeWinner n≤N :=
    max_le (Nat.maxPrimeFac_le.trans (by omega)) (Nat.maxPrimeFac_le.trans (by omega))
  simp only [primeWinnerHarmonicTerm,if_neg (show primeWinner n≠p by omega)]

/-- The finite expression includes every nonzero high-label window current. -/
lemma primeHarmonicWindowL1Above_eq_tsum (B L U : ℕ) (hLU : L≤U) :
    primeHarmonicWindowL1Above B L U =
      ∑' p, if B<p then ‖rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L‖ else 0 := by
  classical
  have hs : (∑' p, if B<p then
      ‖rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L‖ else 0) =
      ∑ p ∈ Ioc B (U+1), if B<p then
        ‖rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L‖ else 0 := by
    apply tsum_eq_sum
    intro p hp
    by_cases hBp : B<p
    · have hUp : U<p := by simp only [mem_Ioc,not_and] at hp; have := hp hBp; omega
      rw [if_pos hBp,rawPrimeWinnerHarmonic_zero_above_endpoint p U hUp,
        rawPrimeWinnerHarmonic_zero_above_endpoint p L (hLU.trans_lt hUp),sub_self,norm_zero]
    · rw [if_neg hBp]
  rw [hs,primeHarmonicWindowL1Above]
  apply sum_congr rfl
  intro p hp
  rw [if_pos (mem_Ioc.mp hp).1]

/-- In particular, the full high-label tail on a bounded-ratio window
vanishes for every cutoff with log(B)/log(U) tending to one. This is a
boundary theorem; no fixed exponent below one meets its hypothesis. -/
theorem primeHarmonicWindowL1Above_log_ratio_zero (B L U : ℕ → ℕ)
    (R : ℝ) (hL : Tendsto L atTop atTop) (hU : Tendsto U atTop atTop)
    (hB : ∀ᶠ N : ℕ in atTop, 0<B N)
    (hratio : Tendsto (fun N => Real.log (B N)/Real.log (U N)) atTop (𝓝 1))
    (hwindow : ∀ᶠ N : ℕ in atTop, L N≤U N ∧ (U N : ℝ)≤R*L N) :
    Tendsto (fun N => primeHarmonicWindowL1Above (B N) (L N) (U N)) atTop (𝓝 0) := by
  apply primeWinnerHarmonicWindow_nearlinear_zero B L U (fun N => Ioc (B N) (U N+1))
    R hL hU
  · filter_upwards [hwindow] with N hN
    exact ⟨hN.1,hN.2,fun _ hp => (mem_Ioc.mp hp).1⟩
  · exact nearlinear_power_bounds_of_log_ratio B U hU hB hratio

/-- The analogous unweighted absolute tail also vanishes, uniformly for
every near-linear cutoff, not merely a fixed cofactor range. -/
theorem primeWinnerL1Above_nearlinear_zero (B U : ℕ → ℕ)
    (hU : Tendsto U atTop atTop)
    (hcut : ∀ u : ℝ, 0<u → ∀ᶠ N : ℕ in atTop, (U N : ℝ)^(1-u)≤B N) :
    Tendsto (fun N => primeWinnerL1Above (B N) (U N)/(U N : ℝ)) atTop (𝓝 0) := by
  have ht := (bothAbove_nearlinear_ratio_zero B U hU hcut).add
    (tendsto_one_div_atTop_nhds_zero_nat.comp hU)
  simp only [add_zero] at ht
  apply squeeze_zero (fun N => by unfold primeWinnerL1Above; positivity) _ ht
  intro N
  have h := div_le_div_of_nonneg_right (primeWinnerL1Above_le_bothAbove (B N) (U N))
    (Nat.cast_nonneg (α := ℝ) (U N))
  simpa only [add_div] using h

theorem primeWinnerL1Above_log_ratio_zero (B U : ℕ → ℕ)
    (hU : Tendsto U atTop atTop) (hB : ∀ᶠ N : ℕ in atTop, 0<B N)
    (hratio : Tendsto (fun N => Real.log (B N)/Real.log (U N)) atTop (𝓝 1)) :
    Tendsto (fun N => primeWinnerL1Above (B N) (U N)/(U N : ℝ)) atTop (𝓝 0) :=
  primeWinnerL1Above_nearlinear_zero B U hU
    (nearlinear_power_bounds_of_log_ratio B U hU hB hratio)

#print axioms primeHarmonicWindowL1Above_eq_tsum
#print axioms primeWinnerL1Above_log_ratio_zero
#print axioms primeHarmonicWindowL1Above_log_ratio_zero
#print axioms primeWinnerL1Above_nearlinear_zero
#print axioms primeWinnerHarmonicWindow_high_bound
#print axioms primeWinnerHarmonicWindow_nearlinear_zero
end Erdos371
