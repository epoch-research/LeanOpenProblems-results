import Submission.BuchstabSharpSource
import Submission.BuchstabPrimeCoordinates
import Submission.FirstHitNormalizedCost

/-! A finite-prefix saving in the complete depth-one refinement error. The
inverse-log-square prime sum removes one reciprocal-prefix factor. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

noncomputable def sharpRefinementCostConstant : ℝ := 4+64*exp 4*inverseLogSquareConstant

lemma sharpRefinementCostConstant_ge : 4 ≤ sharpRefinementCostConstant := by
  have hh := inverseLogSquareConstant_pos
  dsimp only [sharpRefinementCostConstant]
  have h : 0 ≤ 64*exp 4*inverseLogSquareConstant := by positivity
  linarith

lemma scaled_sharp_cost_le_log (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D) :
    scaledSharpSelbergCost nthPrime k D ≤ 64*exp 4*D/(log (nthPrime k : ℝ))^2 := by
  let p := nthPrime k
  let R := selbergCutoff (4*D)
  have hp := nthPrime_prime k
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hD1 : 1 ≤ D := by linarith
  have hlp : 0 < log (p : ℝ) := log_pos hp1
  have hR : 0 < R := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hsqrt : sqrt (p : ℝ) ≤ (R : ℝ) := by
    calc
      _ ≤ sqrt D := sqrt_le_sqrt hpkD
      _ ≤ (⌈sqrt D⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ R := by exact_mod_cast ceiling_sqrt_le_scaledCutoff D hD1
  have hlogR : log (p : ℝ)/2 ≤ log (R : ℝ) := by
    rw [← log_sqrt hp0.le]
    exact log_le_log (sqrt_pos.mpr hp0) hsqrt
  have hG := primeNormalizer_strict_log_lower p R hp hR hlogR
  rw [← nthPrime_normalizer k R] at hG
  let G := normalizer (fun i : Fin k => primeMarginal i.val)
    (divisorSupport (fun i : Fin k => nthPrime i.val) R)
  change log (p : ℝ)/4 ≤ G at hG
  have hb : scaledSelbergBase nthPrime k D ≤ 4/log (p : ℝ) := by
    change 1/G ≤ _
    have hh := one_div_le_one_div_of_le (by positivity : 0 < log (p : ℝ)/4) hG
    convert hh using 1 <;> ring
  have hc := sharpSelbergCost_le_normalized nthPrime nthPrime_prime
    nthPrime_strictMono.injective k (4*D)
  change scaledSharpSelbergCost nthPrime k D ≤
    (exp 2*(R : ℝ)*scaledSelbergBase nthPrime k D)^2 at hc
  have hb0 : 0 ≤ scaledSelbergBase nthPrime k D :=
    (nthPrime_prefix_density_pos k).le.trans
      (scaledSelbergBase_density nthPrime nthPrime_prime k D)
  have hmul := mul_le_mul_of_nonneg_left hb (show 0 ≤ exp 2*(R : ℝ) by positivity)
  have hs := pow_le_pow_left₀ (mul_nonneg (by positivity) hb0) hmul 2
  have hR2 : (R : ℝ)^2 ≤ 4*D := scaledSelbergCost_le k D hD1
  have he : (exp (2 : ℝ))^2 = exp 4 := by rw [← exp_nat_mul]; norm_num
  have hr := mul_le_mul_of_nonneg_left hR2
    (show 0 ≤ 16*exp 4/(log (p : ℝ))^2 by positivity)
  apply hc.trans (hs.trans _)
  simp only [mul_pow,div_pow,he] at *
  convert hr using 1 <;> ring

lemma inverse_log_square_prefix_le (k : ℕ) :
    (∑ i : Fin k, 1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) ≤ inverseLogSquareConstant := by
  rw [nthPrime_prefix_sum (fun p => 1/((p : ℝ)*log p^2))]
  exact prime_inv_log_square_sum_le _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)

/-- The initial lower error now has an absolute linear-level constant,
not a factor growing with the finite prime reciprocal sum. -/
theorem sharp_lower_zero_le_linear (k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0) k D ≤
      sharpRefinementCostConstant*D := by
  classical
  change lowerErrorStep primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) k D ≤ _
  unfold lowerErrorStep
  split_ifs with hk
  · have hD1 := (primeKeep_levels nthPrime nthPrime_prime nthPrime_strictMono k D hk).1
    have hchild (i : Fin k) : (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val := by
      have hp0 : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
      have hi : (nthPrime i.val : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_strictMono i.isLt).le
      have hki : (nthPrime k : ℝ)^2 ≤ D := hk
      change (nthPrime i.val : ℝ) ≤ D*(1/(nthPrime i.val : ℝ))
      rw [mul_one_div]
      apply (le_div_iff₀ hp0).mpr
      nlinarith only [hi,hki,hp0]
    have hs : (∑ i : Fin k, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val)) ≤
        (64*exp 4*D)*inverseLogSquareConstant := by
      calc
        _ ≤ ∑ i : Fin k, (64*exp 4*D)*(1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) := by
          apply sum_le_sum
          intro i hi
          convert scaled_sharp_cost_le_log i.val (D*primeMarginal i.val) (hchild i) using 1
          unfold primeMarginal
          ring
        _ = (64*exp 4*D)*(∑ i : Fin k, 1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) := by rw [mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_log_square_prefix_le k) (by positivity)
    dsimp only [sharpRefinementCostConstant]
    nlinarith only [hs,hD1]
  · exact mul_nonneg ((by norm_num : (0 : ℝ) ≤ 4).trans sharpRefinementCostConstant_ge) hD

lemma sharp_upper_one_le_linear (k K : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 1 ≤ D) :
    upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1 k D ≤
      sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K)*D := by
  have hB : 1 ≤ sharpRefinementCostConstant := (by norm_num : (1 : ℝ) ≤ 4).trans sharpRefinementCostConstant_ge
  have hB0 : 0 ≤ sharpRefinementCostConstant := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  have hD0 : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans hD
  have hZ := prefixReciprocal_nonneg nthPrime K
  change max (scaledSharpSelbergCost nthPrime k D)
    (1+∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0)
        i.val (D*primeMarginal i.val)) ≤ _
  apply max_le
  · have hc := (scaledSharpSelbergCost_le_old nthPrime nthPrime_prime nthPrime_strictMono.injective k D).trans
      (scaledSelbergCost_le k D hD)
    have hh := mul_le_mul_of_nonneg_right sharpRefinementCostConstant_ge hD0
    have hz := mul_nonneg (mul_nonneg hB0 hD0) hZ
    nlinarith only [hc,hh,hz]
  · have hs : (∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0)
          i.val (D*primeMarginal i.val)) ≤
      sharpRefinementCostConstant*D*prefixReciprocal nthPrime K := by
      calc
        _ ≤ ∑ i : Fin k, sharpRefinementCostConstant*(D*primeMarginal i.val) :=
          sum_le_sum (fun i _ => sharp_lower_zero_le_linear i.val _
            (mul_nonneg hD0 (primeMarginal_pos _).le))
        _ = sharpRefinementCostConstant*D*prefixReciprocal nthPrime k := by
          dsimp only [prefixReciprocal,primeMarginal]
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (prefixReciprocal_mono nthPrime hk) (mul_nonneg hB0 hD0)
    have hBD : 1 ≤ sharpRefinementCostConstant*D := one_le_mul_of_one_le_of_one_le hB hD
    nlinarith only [hs,hBD]

/-- Complete depth-one error with two, rather than three, finite reciprocal
factors. The refined main term is unchanged. -/
theorem sharp_lower_one_le_linear (k K : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1) k D ≤
      sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K)^2*D := by
  have hB : 1 ≤ sharpRefinementCostConstant := (by norm_num : (1 : ℝ) ≤ 4).trans sharpRefinementCostConstant_ge
  have hZ := prefixReciprocal_nonneg nthPrime K
  have hh := lowerErrorStep_le_linear_local primeMarginal (primeKeep nthPrime)
    (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1)
    (sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K)) (prefixReciprocal nthPrime K)
    (one_le_mul_of_one_le_of_one_le hB (by linarith)) hZ
    (fun i => (primeMarginal_pos i).le) K
    (fun j hj => prefixReciprocal_mono nthPrime hj)
    (primeKeep_levels nthPrime nthPrime_prime nthPrime_strictMono)
    (fun j hj E hE => sharp_upper_one_le_linear j K hj E hE) k hk D hD
  convert hh using 1
  ring

#print axioms scaled_sharp_cost_le_log
#print axioms sharp_lower_zero_le_linear
#print axioms sharp_lower_one_le_linear
end Erdos970.RecursiveSieve.Buchstab
