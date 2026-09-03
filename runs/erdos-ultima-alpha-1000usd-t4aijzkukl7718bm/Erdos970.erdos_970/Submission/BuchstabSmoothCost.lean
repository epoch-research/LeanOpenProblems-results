import Submission.BuchstabSmoothSource

/-! Complete finite-depth cost bounds with no reciprocal-prefix losses.
The smooth source decay survives both alternating refinement steps. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

noncomputable def smoothLevelShape (k : ℕ) (D : ℝ) : ℝ :=
  D*log (nthPrime k : ℝ)/log D^3

lemma prime_prefix_log_le_six (k : ℕ) :
    (∑ i : Fin k, log (nthPrime i.val : ℝ)/(nthPrime i.val : ℝ)) ≤ 6*log (nthPrime k : ℝ) := by
  let p := nthPrime k
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (nthPrime_prime k).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hY3 : (3 : ℝ) ≤ ((p+1 : ℕ) : ℝ) := by push_cast; linarith
  have hY0 : (0 : ℝ) < ((p+1 : ℕ) : ℝ) := by linarith
  have hY : 1 ≤ log ((p+1 : ℕ) : ℝ) := (le_log_iff_exp_le hY0).mpr (by linarith [exp_one_lt_three])
  have hlY : log ((p+1 : ℕ) : ℝ) ≤ 2*log (p : ℝ) := by
    have hh := log_le_log hY0 (show ((p+1 : ℕ) : ℝ) ≤ (p : ℝ)^2 by push_cast; nlinarith only [hp2])
    rw [log_pow] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hh := bounded_prime_log_sum (fun i : Fin k => nthPrime i.val) (fun i => nthPrime_prime i.val)
    (nthPrime_strictMono.injective.comp Fin.val_injective) (p+1) hY (by
      intro i
      exact (nthPrime_strictMono i.isLt).le.trans (Nat.le_succ _))
  nlinarith only [hh,hlY]

lemma smoothLevelShape_pos (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) : 0 < smoothLevelShape k D := by
  have hp1 : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  have hlp : 0 < log (nthPrime k : ℝ) := log_pos hp1
  have hlD : 0 < log D := log_pos (hp1.trans_le hpkD)
  have hD : 0 < D := by linarith
  unfold smoothLevelShape
  positivity

lemma one_le_twelve_shape (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    1 ≤ 12*smoothLevelShape k D := by
  have hp2 : (2 : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_prime k).two_le
  have hD1 : 1 < D := by linarith
  have hlD : 0 < log D := log_pos hD1
  have hlogp : (1/2 : ℝ) ≤ log (nthPrime k : ℝ) := by
    have hh := log_le_log (by norm_num : (0 : ℝ) < 2) hp2
    linarith [log_two_gt_d9]
  have hh := pow_div_factorial_le_exp (log D) hlD.le 3
  rw [exp_log (by linarith : 0 < D)] at hh
  norm_num only [Nat.factorial,Nat.reduceMul,Nat.cast_ofNat] at hh
  have hm := mul_le_mul_of_nonneg_left hlogp (show 0 ≤ 12*D by linarith)
  unfold smoothLevelShape
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hlD 3)).mpr
  nlinarith only [hh,hm]

lemma shape_child_le (i : ℕ) (D : ℝ) (hD : 1 < D)
    (hchild : (nthPrime i : ℝ) ≤ D/(nthPrime i : ℝ)) :
    smoothLevelShape i (D/(nthPrime i : ℝ)) ≤
      (8*D/log D^3)*(log (nthPrime i : ℝ)/(nthPrime i : ℝ)) := by
  let p := nthPrime i
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (nthPrime_prime i).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hlD : 0 < log D := log_pos hD
  have hE1 : 1 < D/(p : ℝ) := hp1.trans_le hchild
  have hlE : 0 < log (D/(p : ℝ)) := log_pos hE1
  have hpD : (p : ℝ)^2 ≤ D := by
    have hh := (le_div_iff₀ hp0).mp hchild
    nlinarith only [hh]
  have hlog := log_le_log (pow_pos hp0 2) hpD
  rw [log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have heq : log (D/(p : ℝ)) = log D-log (p : ℝ) := log_div (by linarith : D ≠ 0) hp0.ne'
  have hhalf : log D/2 ≤ log (D/(p : ℝ)) := by linarith only [hlog,heq]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ log D/2) hhalf 3
  have hratio : 1/log (D/(p : ℝ))^3 ≤ 8/log D^3 := by
    apply (div_le_div_iff₀ (pow_pos hlE 3) (pow_pos hlD 3)).mpr
    nlinarith only [hpow]
  have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (D/(p : ℝ))*log (p : ℝ) by positivity)
  unfold smoothLevelShape
  convert hm using 1 <;> ring

lemma shape_child_sum (k : ℕ) (D B : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) (hB : 0 ≤ B)
    (F : Fin k → ℝ)
    (hF : ∀ i : Fin k, F i = 0 ∨
      ((nthPrime i.val : ℝ) ≤ D*primeMarginal i.val ∧ F i ≤ B*smoothLevelShape i.val (D*primeMarginal i.val))) :
    (∑ i, F i) ≤ 48*B*smoothLevelShape k D := by
  have hp1 : (1 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).one_lt
  have hD : 1 < D := hp1.trans_le hpkD
  have hlD : 0 < log D := log_pos hD
  have hc : 0 ≤ 8*B*D/log D^3 := by positivity
  have hs : (∑ i, F i) ≤ (8*B*D/log D^3)*(∑ i : Fin k, log (nthPrime i.val : ℝ)/(nthPrime i.val : ℝ)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    rcases hF i with hz | ⟨hchild,hcost⟩
    · rw [hz]
      exact mul_nonneg hc (div_nonneg (log_natCast_nonneg _) (Nat.cast_nonneg _))
    · have hh := shape_child_le i.val D hD (by simpa only [primeMarginal,mul_one_div] using hchild)
      have hm := mul_le_mul_of_nonneg_left hh hB
      apply hcost.trans
      simp only [primeMarginal,mul_one_div] at *
      convert hm using 1 <;> ring
  have hm := mul_le_mul_of_nonneg_left (prime_prefix_log_le_six k) hc
  apply hs.trans
  unfold smoothLevelShape
  convert hm using 1 <;> ring

lemma lowerErrorStep_le_shape (F : ℕ → ℝ → ℝ) (B : ℝ) (hB : 1 ≤ B)
    (hF : ∀ k D, (nthPrime k : ℝ) ≤ D → F k D ≤ B*smoothLevelShape k D)
    (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime) F k D ≤ 60*B*smoothLevelShape k D := by
  classical
  have hshape := smoothLevelShape_pos k D hpkD
  unfold lowerErrorStep
  split_ifs with hkeep
  · have hchild (i : Fin k) : (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val := by
      have hp0 : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
      have hi : (nthPrime i.val : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_strictMono i.isLt).le
      have hki : (nthPrime k : ℝ)^2 ≤ D := hkeep
      change (nthPrime i.val : ℝ) ≤ D*(1/(nthPrime i.val : ℝ))
      rw [mul_one_div]
      apply (le_div_iff₀ hp0).mpr
      nlinarith only [hi,hki,hp0]
    have hs := shape_child_sum k D B hpkD (by linarith) (fun i => F i.val (D*primeMarginal i.val))
      (fun i => Or.inr ⟨hchild i,hF i.val _ (hchild i)⟩)
    have hunit := one_le_twelve_shape k D hpkD
    have hm := mul_le_mul_of_nonneg_right hB hshape.le
    nlinarith only [hs,hunit,hm]
  · positivity

lemma upperError_le_shape (F : ℕ → ℝ → ℝ) (C : ℝ) (hC : 1 ≤ C)
    (hF : ∀ k D, (nthPrime k : ℝ) ≤ D → F k D ≤ C*smoothLevelShape k D)
    (n k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    upperError primeMarginal (primeKeep nthPrime) F n k D ≤
      (C*3600^n)*smoothLevelShape k D := by
  classical
  induction n generalizing k D with
  | zero => simpa only [upperError,pow_zero,mul_one] using hF k D hpkD
  | succ n ih =>
    let B := C*3600^n
    have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by norm_num))
    have hshape := smoothLevelShape_pos k D hpkD
    have hbound := lowerErrorStep_le_shape (upperError primeMarginal (primeKeep nthPrime) F n) B hB ih
    have hs := shape_child_sum k D (60*B) hpkD (by positivity)
      (fun i => lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) F n) i.val (D*primeMarginal i.val)) (by
        intro i
        by_cases hkeep : primeKeep nthPrime i.val (D*primeMarginal i.val)
        · have hp1 : (1 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).one_lt
          have he : (nthPrime i.val : ℝ)^2 ≤ D*primeMarginal i.val := hkeep
          have hpi : (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val := by nlinarith only [hp1,he]
          exact Or.inr ⟨hpi,hbound i.val _ hpi⟩
        · exact Or.inl (by simp only [lowerErrorStep,if_neg hkeep]))
    have hunit := one_le_twelve_shape k D hpkD
    have hm := mul_le_mul_of_nonneg_right hB hshape.le
    change max (upperError primeMarginal (primeKeep nthPrime) F n k D)
      (1+∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) F n) i.val (D*primeMarginal i.val)) ≤ _
    have hid : C*3600^(n+1) = 3600*B := by dsimp only [B]; rw [pow_succ]; ring
    rw [hid]
    apply max_le
    · have hh := ih k D hpkD
      change upperError _ _ _ _ _ _ ≤ B*smoothLevelShape k D at hh
      have hz : 0 ≤ B*smoothLevelShape k D := by positivity
      nlinarith only [hh,hz]
    · nlinarith only [hs,hunit,hm]

lemma smoothLeafConstant_one_ge : 1 ≤ smoothLeafConstant 1 := by
  have hC : 1 ≤ smoothCostConstant := by
    have h2 : 1 ≤ exp (2 : ℝ) := one_le_exp (by norm_num)
    have h20 := exp_pos (20 : ℝ)
    unfold smoothCostConstant
    linarith
  unfold smoothLeafConstant
  norm_num only [Nat.reduceAdd,Nat.factorial,Nat.reduceMul,Nat.cast_ofNat]
  nlinarith only [hC]

/-- Fully charged error at every fixed depth, now O_n(D/log(D)^2) in kept
root ranges. The boundary-prime logarithm is kept for later summation. -/
theorem smooth_refined_lower_cost (n k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n) k D ≤
      (60*smoothLeafConstant 1*3600^n)*smoothLevelShape k D := by
  have hF (j : ℕ) (E : ℝ) (hE : (nthPrime j : ℝ) ≤ E) :
      scaledSharpSelbergCost nthPrime j E ≤ smoothLeafConstant 1*smoothLevelShape j E := by
    have hh := scaled_sharp_cost_le_smooth_power 1 j E hE
    simpa only [smoothLevelShape,Nat.reduceAdd,pow_one,mul_div_assoc,mul_assoc] using hh
  have hC : 1 ≤ smoothLeafConstant 1*3600^n :=
    one_le_mul_of_one_le_of_one_le smoothLeafConstant_one_ge (one_le_pow₀ (by norm_num))
  have hh := lowerErrorStep_le_shape
    (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) n)
    (smoothLeafConstant 1*3600^n) hC
    (fun j E hE => upperError_le_shape _ _ smoothLeafConstant_one_ge hF n j E hE) k D hpkD
  convert hh using 1
  ring

#print axioms smooth_refined_lower_cost
end Erdos970.RecursiveSieve.Buchstab
