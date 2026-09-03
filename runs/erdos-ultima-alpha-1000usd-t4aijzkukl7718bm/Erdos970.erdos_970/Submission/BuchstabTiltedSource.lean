import Submission.SelbergArbitraryTilt
import Submission.BuchstabSmoothSource
import Submission.BuchstabSplitCost

/-! Stronger exponential decay for the actual sharp Selberg source, including
an explicit finite-prefix treatment for a uniform slow exponential profile.
No depth-uniform recursive error or Jacobsthal endpoint is asserted here. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 2000000

lemma scaled_sharp_cost_le_arbitrary_tilt (A : ℝ) (hA : 0 ≤ A) (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D)
    (hAlp : A ≤ log (nthPrime k : ℝ)) :
    scaledSharpSelbergCost nthPrime k D ≤
      64*(smoothTiltConstant A)^2*D*exp (-A*log D/(4*log (nthPrime k : ℝ)))/log (nthPrime k : ℝ)^2 := by
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
  have hc := canonical_cost_le_arbitrary_tilt (fun i : Fin k => nthPrime i.val) (fun i => nthPrime_prime i.val)
    (nthPrime_strictMono.injective.comp Fin.val_injective) A hA Y R hlogY (by
      intro i
      exact (nthPrime_strictMono i.isLt).le.trans (Nat.le_succ _)) hR (hAlp.trans (log_le_log hp0 (by dsimp [Y]; push_cast; linarith)))
  change kernelCost _ _ ≤ (smoothTiltConstant A)*(R : ℝ)*exp (-A*log (R : ℝ)/(2*log (Y : ℝ)))/G at hc
  have hg : 1/G ≤ 4/log (p : ℝ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < log (p : ℝ)/4) hG
    convert hh using 1 <;> ring
  have hnorm := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (smoothTiltConstant A)*(R : ℝ)*exp (-A*log (R : ℝ)/(2*log (Y : ℝ))) by have := smoothTiltConstant_pos A; positivity)
  have hc' : kernelCost (fun i : Fin k => primeMarginal i.val)
      (canonicalOrthogonal (fun i : Fin k => primeMarginal i.val)
        (divisorSupport (fun i : Fin k => nthPrime i.val) R)) ≤
      (4*(smoothTiltConstant A)*(R : ℝ)*exp (-A*log (R : ℝ)/(2*log (Y : ℝ))))/log (p : ℝ) := by
    apply hc.trans
    convert hnorm using 1 <;> ring
  have hs := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hc' 2
  have hexp : (exp (-A*log (R : ℝ)/(2*log (Y : ℝ))))^2 = exp (-A*log (R : ℝ)/log (Y : ℝ)) := by
    rw [← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have he : exp (-A*log (R : ℝ)/log (Y : ℝ)) ≤ exp (-A*log D/(4*log (p : ℝ))) := by
    apply exp_le_exp.mpr
    have hb : -log (R : ℝ)/log (Y : ℝ) ≤ -log D/(4*log (p : ℝ)) := by
      apply (div_le_div_iff₀ hlogYp (by positivity : 0 < 4*log (p : ℝ))).mpr
      have hh := mul_le_mul_of_nonneg_right hlogYupper hlD
      have hr := mul_le_mul_of_nonneg_left hlogR hlp.le
      nlinarith only [hh,hr]
    convert mul_le_mul_of_nonneg_left hb hA using 1 <;> ring
  have hR2 : (R : ℝ)^2 ≤ 4*D := scaledSelbergCost_le k D hD1
  have heR := mul_le_mul hR2 he (exp_pos _).le (by positivity : 0 ≤ 4*D)
  have hscale := mul_le_mul_of_nonneg_left heR
    (show 0 ≤ 16*(smoothTiltConstant A)^2/log (p : ℝ)^2 by positivity)
  change scaledSharpSelbergCost nthPrime k D ≤ _ at hs
  simp only [div_pow,mul_pow,hexp] at hs
  apply hs.trans
  convert hscale using 1 <;> ring



noncomputable def slowLevelShape (k : ℕ) (D : ℝ) : ℝ :=
  D*exp ((-2/3 : ℝ)*log D/log (nthPrime k : ℝ))/log (nthPrime k : ℝ)

lemma prime_log_gt_two_thirds (k : ℕ) : (2/3 : ℝ) < log (nthPrime k : ℝ) := by
  have hp : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_prime k).two_le
  exact (by linarith [log_two_gt_d9] : (2/3 : ℝ) < log 2).trans_le
    (log_le_log (by norm_num) hp)

/-- The physical slow profile absorbs a unit at every admissible prefix,
including prime two. The strict inequality 2/3 < log 2 is used here. -/
lemma one_le_slowLevelShape (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    1 ≤ slowLevelShape k D := by
  let p := nthPrime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (nthPrime_prime k).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (nthPrime_prime k).one_lt
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hD0 : 0 < D := hp0.trans_le hpkD
  have hlD : log (p : ℝ) ≤ log D := log_le_log hp0 hpkD
  have hc : (2/3 : ℝ) ≤ log (p : ℝ) := (prime_log_gt_two_thirds k).le
  have ha : 0 ≤ 1-(2/3 : ℝ)/log (p : ℝ) := by
    have hh := (div_le_one hlp).mpr hc
    linarith
  have hm := mul_le_mul_of_nonneg_right hlD ha
  have he : log D+(-2/3 : ℝ)*log D/log (p : ℝ) ≥ log (p : ℝ)-2/3 := by
    have hid : log (p : ℝ)*(1-(2/3 : ℝ)/log (p : ℝ)) = log (p : ℝ)-2/3 := by field_simp
    rw [hid] at hm
    have hidD : log D*(1-(2/3 : ℝ)/log (p : ℝ)) =
        log D+(-2/3 : ℝ)*log D/log (p : ℝ) := by ring
    rwa [hidD] at hm
  have hph : 2*log (p : ℝ) ≤ p := by
    have hh := quadratic_le_exp_of_nonneg hlp.le
    rw [exp_log hp0] at hh
    nlinarith only [hh,sq_nonneg (log (p : ℝ)-1)]
  have hhalf : (1/2 : ℝ) ≤ exp (-(2/3 : ℝ)) := by
    have hc2 : (2/3 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have hh := exp_le_exp.mpr (neg_le_neg hc2)
    simpa only [exp_neg,exp_log (by norm_num : (0 : ℝ) < 2),one_div] using hh
  have hpow : log (p : ℝ) ≤ (p : ℝ)*exp (-(2/3 : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hhalf hp0.le
    linarith only [hph,hh]
  have hexp := exp_le_exp.mpr he
  rw [exp_add,exp_log hD0,sub_eq_add_neg,exp_add,exp_log hp0] at hexp
  unfold slowLevelShape
  apply (le_div_iff₀ hlp).mpr
  simpa only [one_mul] using hpow.trans hexp

lemma small_log_index_bound (k : ℕ) (hk : log (nthPrime k : ℝ) < 4) : k ≤ 81 := by
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hp := exp_lt_exp.mpr hk
  rw [exp_log hp0] at hp
  have he : exp (4 : ℝ) < 81 := by
    have hh := pow_lt_pow_left₀ exp_one_lt_three (exp_pos 1).le (by norm_num : (4 : ℕ) ≠ 0)
    rw [← exp_nat_mul] at hh
    norm_num at hh
    exact hh
  have hkR : (k : ℝ) ≤ nthPrime k := by exact_mod_cast nthPrime_strictMono.id_le k
  have hh : (k : ℝ) ≤ 81 := by linarith
  exact_mod_cast hh

noncomputable def slowSourceConstant : ℝ := 64*(smoothTiltConstant 4)^2+4^81

lemma slowSourceConstant_ge_one : 1 ≤ slowSourceConstant := by
  unfold slowSourceConstant
  have hh : (1 : ℝ) ≤ 4^81 := one_le_pow₀ (by norm_num)
  nlinarith only [sq_nonneg (smoothTiltConstant 4),hh]

/-- An unconditional slow exponential envelope for every actual canonical
source. No boundary-prime threshold or small-prefix exception remains. -/
theorem scaled_sharp_cost_le_slow_profile (k : ℕ) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) :
    scaledSharpSelbergCost nthPrime k D ≤ slowSourceConstant*slowLevelShape k D := by
  have hshape := one_le_slowLevelShape k D hpkD
  have hshape0 : 0 ≤ slowLevelShape k D := by linarith
  by_cases hl : (4 : ℝ) ≤ log (nthPrime k : ℝ)
  · let p := nthPrime k
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (nthPrime_prime k).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 < log (p : ℝ) := log_pos hp1
    have hD0 : 0 ≤ D := hp0.le.trans hpkD
    have hlD : 0 ≤ log D := log_nonneg (hp1.le.trans hpkD)
    have hh := scaled_sharp_cost_le_arbitrary_tilt 4 (by norm_num) k D hpkD hl
    have he : exp (-4*log D/(4*log (p : ℝ))) ≤
        exp ((-2/3 : ℝ)*log D/log (p : ℝ)) := by
      apply exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : 0 < 4*log (p : ℝ)) hlp).mpr
      nlinarith only [mul_nonneg hlD hlp.le]
    have hc : 0 ≤ 64*(smoothTiltConstant 4)^2*D := by positivity
    have hmul := mul_le_mul_of_nonneg_left he hc
    have hs := div_le_div_of_nonneg_right hmul (sq_nonneg (log (p : ℝ)))
    have hsq : log (p : ℝ) ≤ log (p : ℝ)^2 := by nlinarith only [hl]
    have hdiv := div_le_div_of_nonneg_left
      (show 0 ≤ 64*(smoothTiltConstant 4)^2*D*exp ((-2/3 : ℝ)*log D/log (p : ℝ)) by positivity)
      hlp hsq
    have hlarge : scaledSharpSelbergCost nthPrime k D ≤
        (64*(smoothTiltConstant 4)^2)*slowLevelShape k D := by
      apply (hh.trans hs).trans
      convert hdiv using 1 <;> dsimp only [slowLevelShape,p] <;> ring
    apply hlarge.trans
    apply mul_le_mul_of_nonneg_right _ hshape0
    unfold slowSourceConstant
    exact le_add_of_nonneg_right (by positivity)
  · have hk := small_log_index_bound k (lt_of_not_ge hl)
    have hh := (scaled_sharp_cost_le_four_pow k D).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hk)
    have hm := mul_le_mul_of_nonneg_left hshape (by positivity : (0 : ℝ) ≤ 4^81)
    have hsmall : scaledSharpSelbergCost nthPrime k D ≤ (4 : ℝ)^81*slowLevelShape k D :=
      hh.trans (by simpa only [mul_one] using hm)
    apply hsmall.trans
    apply mul_le_mul_of_nonneg_right _ hshape0
    unfold slowSourceConstant
    exact le_add_of_nonneg_left (by positivity)


lemma one_add_sum_four_pow_le (k : ℕ) :
    1+(∑ i : Fin k,(4 : ℝ)^i.val) ≤ (4 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ,Fin.val_zero,pow_zero]
    have he : (∑ i : Fin k,(4 : ℝ)^i.succ.val) = 4*(∑ i : Fin k,(4 : ℝ)^i.val) := by
      simp only [Fin.val_succ,pow_succ,mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    rw [he,pow_succ]
    linarith only [ih]

lemma lowerErrorStep_le_four_pow (F : ℕ → ℝ → ℝ)
    (hF : ∀ k D, F k D ≤ (4 : ℝ)^k) (k : ℕ) (D : ℝ) :
    lowerErrorStep primeMarginal (primeKeep nthPrime) F k D ≤ (4 : ℝ)^k := by
  classical
  unfold lowerErrorStep
  split_ifs
  · exact (add_le_add (le_refl (1 : ℝ)) (sum_le_sum (fun i _ => hF i.val _))).trans
      (one_add_sum_four_pow_le k)
  · positivity

/-- The entire actual positive error recurrence is uniformly bounded in depth
at each fixed prime prefix. This supplies the finite-prefix part of a future
slow-profile induction without discarding its unit terms or outer maximum. -/
theorem complete_sharp_error_le_four_pow (n k : ℕ) (D : ℝ) :
    upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n k D ≤
      (4 : ℝ)^k := by
  induction n generalizing k D with
  | zero => exact scaled_sharp_cost_le_four_pow k D
  | succ n ih =>
    apply max_le (ih k D)
    exact (add_le_add (le_refl (1 : ℝ)) (sum_le_sum (fun i _ =>
      lowerErrorStep_le_four_pow _ ih i.val _))).trans (one_add_sum_four_pow_le k)

#print axioms complete_sharp_error_le_four_pow

#print axioms scaled_sharp_cost_le_arbitrary_tilt
#print axioms one_le_slowLevelShape
#print axioms scaled_sharp_cost_le_slow_profile

end Erdos970.RecursiveSieve.Buchstab
