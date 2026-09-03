import Submission.SelbergSmoothKernel
import Submission.BuchstabSharpCost

/-! Exponential and arbitrarily high power decay in the logarithmic source
level. The actual canonical Selberg sources and mains are unchanged. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

lemma scaled_sharp_cost_le_smooth_exp (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    scaledSharpSelbergCost nthPrime k D ≤
      64*smoothCostConstant^2*D*exp (-log D/(4*log (nthPrime k : ℝ)))/log (nthPrime k : ℝ)^2 := by
  let p := nthPrime k
  let Y := p+1
  let R := selbergCutoff (4*D)
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hD1 : 1 ≤ D := by linarith
  have hD0 : 0 < D := by linarith
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hlD : 0 ≤ log D := log_nonneg hD1
  have hY3 : (3 : ℝ) ≤ Y := by dsimp only [Y]; push_cast; linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 1 ≤ log (Y : ℝ) := (le_log_iff_exp_le hY0).mpr (by linarith [exp_one_lt_three])
  have hlogYp : 0 < log (Y : ℝ) := by linarith
  have hlogYupper : log (Y : ℝ) ≤ 2*log (p : ℝ) := by
    have hy : (Y : ℝ) ≤ (p : ℝ)^2 := by dsimp only [Y]; push_cast; nlinarith only [hp2]
    have hh := log_le_log hY0 hy
    rw [log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hR : 0 < R := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hsqrt : sqrt D ≤ (R : ℝ) := by
    calc
      _ ≤ (⌈sqrt D⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ R := by exact_mod_cast ceiling_sqrt_le_scaledCutoff D hD1
  have hlogR : log D/2 ≤ log (R : ℝ) := by
    rw [← log_sqrt hD0.le]
    exact log_le_log (sqrt_pos.mpr hD0) hsqrt
  have hlogRp : log (p : ℝ)/2 ≤ log (R : ℝ) := by
    have hh := log_le_log hp0 hpkD
    linarith only [hh,hlogR]
  have hG := primeNormalizer_strict_log_lower p R hp hR hlogRp
  rw [← nthPrime_normalizer k R] at hG
  let G := normalizer (fun i : Fin k => primeMarginal i.val)
    (divisorSupport (fun i : Fin k => nthPrime i.val) R)
  change log (p : ℝ)/4 ≤ G at hG
  have hG0 : 0 < G := by linarith
  have hc := canonical_cost_le_smooth (fun i : Fin k => nthPrime i.val) (fun i => nthPrime_prime i.val)
    (nthPrime_strictMono.injective.comp Fin.val_injective) Y R hlogY (by
      intro i
      exact (nthPrime_strictMono i.isLt).le.trans (Nat.le_succ _)) hR
  change kernelCost _ _ ≤ smoothCostConstant*(R : ℝ)*exp (-log (R : ℝ)/(2*log (Y : ℝ)))/G at hc
  have hg : 1/G ≤ 4/log (p : ℝ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < log (p : ℝ)/4) hG
    convert hh using 1 <;> ring
  have hnorm := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ smoothCostConstant*(R : ℝ)*exp (-log (R : ℝ)/(2*log (Y : ℝ))) by have := smoothCostConstant_pos; positivity)
  have hc' : kernelCost (fun i : Fin k => primeMarginal i.val)
      (canonicalOrthogonal (fun i : Fin k => primeMarginal i.val)
        (divisorSupport (fun i : Fin k => nthPrime i.val) R)) ≤
      (4*smoothCostConstant*(R : ℝ)*exp (-log (R : ℝ)/(2*log (Y : ℝ))))/log (p : ℝ) := by
    apply hc.trans
    convert hnorm using 1 <;> ring
  have hs := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hc' 2
  have hexp : (exp (-log (R : ℝ)/(2*log (Y : ℝ))))^2 = exp (-log (R : ℝ)/log (Y : ℝ)) := by
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have he : exp (-log (R : ℝ)/log (Y : ℝ)) ≤ exp (-log D/(4*log (p : ℝ))) := by
    apply exp_le_exp.mpr
    apply (div_le_div_iff₀ hlogYp (by positivity : 0 < 4*log (p : ℝ))).mpr
    have hh := mul_le_mul_of_nonneg_right hlogYupper hlD
    have hr := mul_le_mul_of_nonneg_left hlogR hlp.le
    nlinarith only [hh,hr]
  have hR2 : (R : ℝ)^2 ≤ 4*D := scaledSelbergCost_le k D hD1
  have heR := mul_le_mul hR2 he (exp_pos _).le (by positivity : 0 ≤ 4*D)
  have hscale := mul_le_mul_of_nonneg_left heR
    (show 0 ≤ 16*smoothCostConstant^2/log (p : ℝ)^2 by positivity)
  change scaledSharpSelbergCost nthPrime k D ≤ _ at hs
  simp only [div_pow,mul_pow,hexp] at hs
  apply hs.trans
  convert hscale using 1 <;> ring

noncomputable def smoothLeafConstant (a : ℕ) : ℝ :=
  64*smoothCostConstant^2*((a+2).factorial : ℝ)*4^(a+2)

lemma smoothLeafConstant_pos (a : ℕ) : 0 < smoothLeafConstant a := by
  have := smoothCostConstant_pos
  have hf : (0 : ℝ) < (a+2).factorial := by exact_mod_cast Nat.factorial_pos (a+2)
  unfold smoothLeafConstant
  positivity

lemma exp_neg_div_power_bound (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (n : ℕ) :
    exp (-u/v) ≤ (n.factorial : ℝ)*v^n/u^n := by
  have hh := pow_div_factorial_le_exp (u/v) (div_nonneg hu.le hv.le) n
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hm := mul_le_mul_of_nonneg_left hh (exp_pos (-(u/v))).le
  have he : exp (-(u/v))*exp (u/v) = 1 := by rw [← exp_add,neg_add_cancel,exp_zero]
  rw [he] at hm
  have hpow : 0 < u^n := pow_pos hu n
  have hvpow : 0 < v^n := pow_pos hv n
  rw [div_pow] at hm
  apply (le_div_iff₀ hpow).mpr
  have hz := (mul_le_mul_iff_right₀ (mul_pos hvpow hfac)).mpr hm
  field_simp at hz
  convert hz using 1 <;> ring

/-- An arbitrarily high logarithmic decay exponent for every actual source
whose level is at least its boundary prime. This is uniform in the prefix. -/
theorem scaled_sharp_cost_le_smooth_power (a k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    scaledSharpSelbergCost nthPrime k D ≤
      smoothLeafConstant a*D*log (nthPrime k : ℝ)^a/log D^(a+2) := by
  have hp1 : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  have hlp : 0 < log (nthPrime k : ℝ) := log_pos hp1
  have hD1 : 1 < D := hp1.trans_le hpkD
  have hD : 0 ≤ D := by linarith
  have hlD : 0 < log D := log_pos hD1
  have he := exp_neg_div_power_bound (log D) (4*log (nthPrime k : ℝ)) hlD (by positivity) (a+2)
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ 64*smoothCostConstant^2*D/log (nthPrime k : ℝ)^2 by positivity)
  apply (scaled_sharp_cost_le_smooth_exp k D hpkD).trans
  convert hm using 1
  · ring
  · unfold smoothLeafConstant
    rw [mul_pow,pow_add (log (nthPrime k : ℝ)) a 2]
    field_simp

#print axioms scaled_sharp_cost_le_smooth_exp
#print axioms scaled_sharp_cost_le_smooth_power
end Erdos970.RecursiveSieve.Buchstab
