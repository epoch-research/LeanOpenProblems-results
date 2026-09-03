import Submission.BuchstabProfileTransfer
import Submission.FirstHitNormalizedCost
import Submission.ContinuousBuchstabIteration

/-! The actual canonical upper source is dominated by the initial exponential
continuous envelope. Both the small-level normalizer and the Rankin tail are
proved uniformly in the real logarithmic level. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1000000

lemma buchstabBaseRatio_coarse (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 1 ≤ s)
    (hEuler : eulerMass (p+1).primesBelow ≤ (9/5 : ℝ)*log (p : ℝ)) :
    buchstabBaseRatio p s ≤ 8 := by
  let N := buchstabPrimeCutoff p s
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hlogN : log (p : ℝ)/2 ≤ log (N : ℝ) := by
    have hh := buchstabPrimeCutoff_log_lower p s
    change s/2*log (p : ℝ) ≤ log (N : ℝ) at hh
    nlinarith only [hh,hs,hlp]
  have hG := primeNormalizer_strict_log_lower p N hp (buchstabPrimeCutoff_pos p s) hlogN
  have hG0 : 0 < primeNormalizer p.primesBelow N := (by linarith : 0 < log (p : ℝ)/4).trans_le hG
  have hE := (eulerMass_strict_prefix_le p hp).trans hEuler
  unfold buchstabBaseRatio
  change eulerMass p.primesBelow/primeNormalizer p.primesBelow N ≤ 8
  apply (div_le_iff₀ hG0).mpr
  nlinarith only [hG,hE,hlp]

lemma buchstabBaseRatio_rankin (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 6 ≤ s)
    (hLp : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ)) :
    buchstabBaseRatio p s ≤ 1+(exp 6/3)*exp (-s) := by
  let N := buchstabPrimeCutoff p s
  let E := eulerMass p.primesBelow
  let G := primeNormalizer p.primesBelow N
  let u := log (N : ℝ)/log (p : ℝ)
  have hN : 0 < N := buchstabPrimeCutoff_pos p s
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hu : s/2 ≤ u := (le_div_iff₀ hlp).mpr (buchstabPrimeCutoff_log_lower p s)
  have hlog : log (N : ℝ) = u*log (p : ℝ) := by dsimp [u]; field_simp
  have hE : 0 < E := eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have hr := (strict_normalizer_reciprocal_rankin p N hp hN hLp u (by linarith) hlog).2
  have hm := mul_le_mul_of_nonneg_left hr hE.le
  have he : E*(1/G-1/E)=E/G-1 := by field_simp
  change E*(1/G-1/E) ≤ E*(exp (-2*(u-3))/(3*E)) at hm
  rw [he] at hm
  have hh : E/G-1 ≤ exp (-2*(u-3))/3 := by
    convert hm using 1 <;> field_simp
  have hexp : exp (-2*(u-3)) ≤ exp 6*exp (-s) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith only [hu])
  have hd := div_le_div_of_nonneg_right hexp (by norm_num : (0 : ℝ) ≤ 3)
  change E/G ≤ _
  nlinarith only [hh,hd]

lemma le_exp_envelope_of_mul (x s C : ℝ) (h : x*exp s ≤ C) : x ≤ C*exp (-s) := by
  have hh := mul_le_mul_of_nonneg_right h (exp_pos (-s)).le
  rw [mul_assoc,← exp_add,add_neg_cancel,exp_zero,mul_one] at hh
  exact hh

lemma exp_nat_le_three_pow (n : ℕ) : exp (n : ℝ) ≤ (3 : ℝ)^n := by
  have hp := pow_le_pow_left₀ (exp_pos 1).le exp_one_lt_three.le n
  simpa only [← exp_nat_mul, mul_one] using hp

lemma buchstabBaseRatio_exponential (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 1 ≤ s)
    (hLp : 20000*firstHitProfileError ≤ log (p : ℝ))
    (hLp' : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hEuler : eulerMass (p+1).primesBelow ≤ (9/5 : ℝ)*log (p : ℝ)) :
    buchstabBaseRatio p s ≤ 1+2000*exp (-s) := by
  by_cases h5 : s ≤ 5
  · have hB := buchstabBaseRatio_coarse p hp s hs hEuler
    have hE : exp s ≤ 243 := (exp_le_exp.mpr h5).trans (by convert exp_nat_le_three_pow 5 using 1 <;> norm_num)
    have h7 : (7 : ℝ) ≤ 2000*exp (-s) := le_exp_envelope_of_mul 7 s 2000 (by linarith only [hE])
    linarith only [hB,h7]
  by_cases h6 : s ≤ 6
  · have hbase := buchstabBaseRatio_middle p hp 2 (by norm_num) (by norm_num) hLp hEuler
    norm_num [firstHitFullProfile] at hbase
    have hB : buchstabBaseRatio p s ≤ 2 :=
      ((buchstabBaseRatio_antitone p hp) (by linarith : (2 : ℝ) ≤ s)).trans (by linarith only [hbase])
    have hE : exp s ≤ 729 := (exp_le_exp.mpr h6).trans (by convert exp_nat_le_three_pow 6 using 1 <;> norm_num)
    have h1 : (1 : ℝ) ≤ 2000*exp (-s) := le_exp_envelope_of_mul 1 s 2000 (by linarith only [hE])
    linarith only [hB,h1]
  · have hB := buchstabBaseRatio_rankin p hp s (by linarith) hLp'
    have hE : exp 6 ≤ 729 := by convert exp_nat_le_three_pow 6 using 1 <;> norm_num
    have hm := mul_le_mul_of_nonneg_right (show exp 6/3 ≤ 2000 by linarith only [hE]) (exp_pos (-s)).le
    linarith only [hB,hm]

/-- A single prime threshold controls every logarithmic level at least one. -/
theorem exists_referenceUpper_exponential_source :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      referenceUpper 0 k (exp (s*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*(1+ContinuousBuchstab.upperEnvelope 0 s) := by
  have hlog : Tendsto (fun p : ℕ => log (p : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((hlog.eventually_ge_atTop (20000*firstHitProfileError)).and
      ((hlog.eventually_ge_atTop (50*WeightedMertens.sharpMomentError)).and
        eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun k hk s hs => ?_⟩
  obtain ⟨h1,h2,h3⟩ := hN (nthPrime k) hk
  have hb := scaled_base_le_normalized_profile k s (by linarith)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (buchstabBaseRatio_exponential _ (nthPrime_prime k) s hs h1 h2 h3)
    (nthPrime_prefix_density_pos k).le)

#print axioms buchstabBaseRatio_exponential
#print axioms exists_referenceUpper_exponential_source
end Erdos970.RecursiveSieve.Buchstab
