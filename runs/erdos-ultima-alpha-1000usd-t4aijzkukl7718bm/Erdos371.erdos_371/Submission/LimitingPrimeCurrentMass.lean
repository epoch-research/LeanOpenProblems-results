import Submission.UniformPrimeCurrentHead

/-! The absolute mass of the limiting prime-current vector is sublogarithmic
in the prime cutoff. This is weaker than summability or tail tightness. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

lemma rawPrimeWinnerHarmonic_eq_normalized (p N : ℕ) :
    rawPrimeWinnerHarmonic p (N+2) =
      (harmonic (N+1) : ℝ)*primeWinnerHarmonicCurrent N p := by
  have hs : (∑ n ∈ Icc 1 (N+1), (if primeWinner n=p then factorSign n else 0)/(n : ℝ)) =
      rawPrimeWinnerHarmonic p (N+2) := by
    rw [show Icc 1 (N+1)=Ico 1 (N+2) by ext n; simp; omega,
      sum_Ico_eq_sub _ (by omega)]
    simp only [rawPrimeWinnerHarmonic,primeWinnerHarmonicTerm,ite_div,zero_div,
      sum_range_one,Nat.cast_zero,div_zero,ite_self,sub_zero]
  rw [primeWinnerHarmonicCurrent,harmonicMean,hs]
  exact (mul_div_cancel₀ _ (harmonic_real_pos N).ne').symm

lemma rawPrimeWinnerHarmonic_head_norm_bound (B N : ℕ) (hBN : B≤N+2) :
    (∑ p ∈ range (B+1), ‖rawPrimeWinnerHarmonic p (N+2)‖) ≤
      (harmonic (N+1) : ℝ)*(∑ p ∈ range (N+3), |primeWinnerHarmonicCurrent N p|) := by
  have hh : (0 : ℝ)≤harmonic (N+1) := (harmonic_real_pos N).le
  simp only [rawPrimeWinnerHarmonic_eq_normalized,norm_mul,Real.norm_eq_abs,abs_of_nonneg hh,← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hh
  exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => abs_nonneg _)

lemma harmonic_power_log_bound (B K : ℕ) (hB : 0<B) :
    (harmonic ((B+1)^K+1) : ℝ)/Real.log (B+1 : ℝ) ≤
      (K : ℝ)+(1+Real.log 2)/Real.log 2 := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2≤Real.log (B+1 : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤B+1 by omega))
  have hlB : 0<Real.log (B+1 : ℝ) := hl2.trans_le hlog
  have hpow1 : (1 : ℝ)≤(B+1 : ℝ)^K := one_le_pow₀ (by exact_mod_cast (show 1≤B+1 by omega))
  have hlogpow : Real.log (((B+1)^K+1 : ℕ) : ℝ) ≤ Real.log 2+(K : ℝ)*Real.log (B+1 : ℝ) := by
    push_cast
    calc
      _ ≤ Real.log (2*(B+1 : ℝ)^K) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  have h := div_le_div_of_nonneg_right ((harmonic_le_one_add_log ((B+1)^K+1)).trans (add_le_add le_rfl hlogpow)) hlB.le
  have hdiv : (1+Real.log 2)/Real.log (B+1 : ℝ) ≤ (1+Real.log 2)/Real.log 2 :=
    div_le_div_of_nonneg_left (by positivity) hl2 hlog
  calc
    _ ≤ (1+(Real.log 2+(K : ℝ)*Real.log (B+1 : ℝ)))/Real.log (B+1 : ℝ) := h
    _ = (K : ℝ)+(1+Real.log 2)/Real.log (B+1 : ℝ) := by field_simp; ring
    _ ≤ _ := add_le_add le_rfl hdiv

lemma raw_prime_current_power_head_sublogarithmic (K : ℕ) (hK : 0<K) :
    Tendsto (fun B => (∑ p ∈ range (B+1), ‖rawPrimeWinnerHarmonic p ((B+1)^K+2)‖)/
      Real.log (B+1 : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℕ => (B+1)^K) atTop atTop :=
    tendsto_atTop_mono (fun B => Nat.le_succ B |>.trans (Nat.le_pow hK)) tendsto_id
  have hnorm := primeWinner_harmonic_l1_zero.comp ht
  have hlim := hnorm.const_mul ((K : ℝ)+(1+Real.log 2)/Real.log 2)
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall (fun B => div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))
      (Real.log_nonneg (by exact_mod_cast (show 1≤B+1 by omega))))
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with B hB
    have hlB : 0<Real.log (B+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<B+1 by omega))
    have hBpow : B≤(B+1)^K+2 :=
      ((Nat.le_succ B).trans (Nat.le_pow hK)).trans (Nat.le_add_right _ _)
    have he := div_le_div_of_nonneg_right
      (rawPrimeWinnerHarmonic_head_norm_bound B ((B+1)^K) hBpow) hlB.le
    calc
      _ ≤ (harmonic ((B+1)^K+1) : ℝ)*
          (∑ p ∈ range ((B+1)^K+3), |primeWinnerHarmonicCurrent ((B+1)^K) p|)/Real.log (B+1 : ℝ) := he
      _ = ((harmonic ((B+1)^K+1) : ℝ)/Real.log (B+1 : ℝ))*
          (∑ p ∈ range ((B+1)^K+3), |primeWinnerHarmonicCurrent ((B+1)^K) p|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (harmonic_power_log_bound B K hB)
        (sum_nonneg (fun _ _ => abs_nonneg _))

lemma prime_current_power_head_error_bound (B K : ℕ) (hB : 0<B) :
    primeCurrentHeadError B ((B+1)^K+2)/Real.log (B+1 : ℝ) ≤
      (4*Real.exp 4/Real.log 2)*Real.exp (-Real.log 2*(K : ℝ)/32) := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2≤Real.log (B+1 : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤B+1 by omega))
  have hlB : 0<Real.log (B+1 : ℝ) := hl2.trans_le hlog
  have hN : 0<(B+1)^K+2 := by omega
  have hscale : (K : ℝ)*Real.log (B+1 : ℝ)≤Real.log (((B+1)^K+2 : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have he : Real.exp (-Real.log 2*Real.log (((B+1)^K+2 : ℕ) : ℝ)/(32*Real.log (B+1 : ℝ))) ≤
      Real.exp (-Real.log 2*(K : ℝ)/32) := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<32*Real.log (B+1 : ℝ))).mpr
    have hm := mul_le_mul_of_nonpos_left hscale (neg_nonpos.mpr hl2.le)
    convert hm using 1
    ring
  have hcoef : (1+Real.log (B+1 : ℝ)/Real.log 2)/Real.log (B+1 : ℝ) ≤ 2/Real.log 2 := by
    have hi := one_div_le_one_div_of_le hl2 hlog
    calc
      _ = 1/Real.log (B+1 : ℝ)+1/Real.log 2 := by field_simp
      _ ≤ 1/Real.log 2+1/Real.log 2 := add_le_add hi le_rfl
      _ = _ := by ring
  calc
    _ ≤ (2*Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2) *
          Real.exp (-Real.log 2*Real.log (((B+1)^K+2 : ℕ) : ℝ)/(32*Real.log (B+1 : ℝ))))/Real.log (B+1 : ℝ) :=
        div_le_div_of_nonneg_right (primeCurrentHeadError_uniform_bound B _ hB hN) hlB.le
    _ ≤ (2*Real.exp 4*(1+Real.log (B+1 : ℝ)/Real.log 2)*Real.exp (-Real.log 2*(K : ℝ)/32))/Real.log (B+1 : ℝ) := by gcongr
    _ = 2*Real.exp 4*((1+Real.log (B+1 : ℝ)/Real.log 2)/Real.log (B+1 : ℝ))*
          Real.exp (-Real.log 2*(K : ℝ)/32) := by ring
    _ ≤ 2*Real.exp 4*(2/Real.log 2)*Real.exp (-Real.log 2*(K : ℝ)/32) := by gcongr
    _ = _ := by ring

noncomputable def limitingPrimeCurrentAbsPrefix (B : ℕ) : ℝ :=
  ∑ p ∈ range (B+1), ‖primeWinnerHarmonicLimit p‖

lemma limitingPrimeCurrentAbsPrefix_le (B N : ℕ) :
    limitingPrimeCurrentAbsPrefix B ≤
      (∑ p ∈ range (B+1), ‖rawPrimeWinnerHarmonic p N‖)+primeCurrentHeadError B N := by
  rw [limitingPrimeCurrentAbsPrefix,primeCurrentHeadError,← sum_add_distrib]
  apply sum_le_sum
  intro p _
  simpa only [add_sub_cancel] using norm_add_le (rawPrimeWinnerHarmonic p N)
    (primeWinnerHarmonicLimit p-rawPrimeWinnerHarmonic p N)

/-- Signed harmonic cancellation and uniform smooth tails control the
absolute limiting-current mass on the logarithmic scale of the labels.
No unnormalized l1 summability is asserted. -/
theorem limiting_prime_current_mass_sublogarithmic :
    Tendsto (fun B => limitingPrimeCurrentAbsPrefix B/Real.log (B+1 : ℝ)) atTop (𝓝 0) := by
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : 0≤Real.exp (-Real.log 2/32) := (Real.exp_pos _).le
  have hr1 : Real.exp (-Real.log 2/32)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (4*Real.exp 4/Real.log 2)
  simp only [mul_zero] at ht
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,hsmall⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2))).exists
  have hexp : Real.exp (-Real.log 2*(K : ℝ)/32)=Real.exp (-Real.log 2/32)^K := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hexp] at hsmall
  have hraw := raw_prime_current_power_head_sublogarithmic K hK
  filter_upwards [eventually_gt_atTop (0 : ℕ),hraw.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)]
    with B hB hrawB
  have hlB : 0<Real.log (B+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1<B+1 by omega))
  have hnonneg : 0≤limitingPrimeCurrentAbsPrefix B/Real.log (B+1 : ℝ) :=
    div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) hlB.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  have hb := div_le_div_of_nonneg_right (limitingPrimeCurrentAbsPrefix_le B ((B+1)^K+2)) hlB.le
  rw [add_div] at hb
  have he := prime_current_power_head_error_bound B K hB
  linarith

#print axioms raw_prime_current_power_head_sublogarithmic
#print axioms limiting_prime_current_mass_sublogarithmic
end Erdos371
