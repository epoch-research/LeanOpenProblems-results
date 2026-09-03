import Submission.BuchstabSharpCost
import Submission.FirstHitTwoScaleCost

/-! A small-prefix / large-prime split for the complete sharp refinement error.
No modification to the main term or to the selected-error maximum is made. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

lemma sharpSelbergCost_le_four_pow (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (k : ℕ) (D : ℝ) : sharpSelbergCost p k D ≤ (4 : ℝ)^k := by
  have hR : 0 < selbergCutoff D := (by norm_num : 0 < (1 : ℕ)).trans_le (le_max_left _ _)
  have hq := prime_marginals (fun i : Fin k => p i.val) (fun i => hp i.val)
  have hc := canonical_cost_le_card _ hq _ (divisorSupport_nonempty _ _ hR)
    (divisorSupport_downward _ (fun i : Fin k => (hp i.val).pos) _)
  have hcard : (divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D)).card ≤ 2^k := by
    have hh := card_le_univ (divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D))
    simpa using hh
  have hh := hc.trans (show ((divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D)).card : ℝ) ≤ (2 : ℝ)^k by exact_mod_cast hcard)
  have hs := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hh 2
  change sharpSelbergCost p k D ≤ _ at hs
  convert hs using 1
  rw [← pow_mul, mul_comm k 2, pow_mul]
  norm_num

lemma scaled_sharp_cost_le_four_pow (k : ℕ) (D : ℝ) :
    scaledSharpSelbergCost nthPrime k D ≤ (4 : ℝ)^k :=
  sharpSelbergCost_le_four_pow nthPrime nthPrime_prime k (4*D)

noncomputable def splitEarlyCost (J : ℕ) : ℝ := 1+((J : ℝ)+1)*4^J
noncomputable def splitTailCost (J : ℕ) : ℝ := 64*exp 4*inverseLogSquareConstant/log (J : ℝ)^2

lemma splitEarlyCost_ge (J : ℕ) : 1 ≤ splitEarlyCost J := by
  unfold splitEarlyCost
  have : 0 ≤ ((J : ℝ)+1)*4^J := by positivity
  linarith

lemma splitTailCost_nonneg (J : ℕ) : 0 ≤ splitTailCost J := by
  unfold splitTailCost
  have := inverseLogSquareConstant_pos
  positivity

lemma split_child_sum (J k : ℕ) (hJ : 2 ≤ (J : ℝ)) (hlJ : 1 ≤ log (J : ℝ))
    (D : ℝ) (hD : 0 ≤ D)
    (hchild : ∀ i : Fin k, (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val) :
    (∑ i : Fin k, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val)) ≤
      ((J : ℝ)+1)*4^J+splitTailCost J*D := by
  classical
  let S : Finset (Fin k) := univ.filter (fun i => i.val ≤ J)
  let T : Finset (Fin k) := univ.filter (fun i => ¬i.val ≤ J)
  have hcard : S.card ≤ J+1 := by
    have hh := card_le_card_of_injOn (s := S) (t := range (J+1)) (f := Fin.val)
      (fun i hi => mem_range.mpr (by have : i.val ≤ J := (mem_filter.mp (show i ∈ S from hi)).2; omega))
      Fin.val_injective.injOn
    simpa using hh
  have hs : (∑ i ∈ S, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val)) ≤
      ((J : ℝ)+1)*4^J := by
    calc
      _ ≤ ∑ _i ∈ S, (4 : ℝ)^J := sum_le_sum (fun i hi =>
        (scaled_sharp_cost_le_four_pow i.val _).trans
          (pow_le_pow_right₀ (by norm_num) (mem_filter.mp hi).2))
      _ = (S.card : ℝ)*4^J := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have htail : (∑ i ∈ T, 1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) ≤
      inverseLogSquareConstant/log (J : ℝ)^2 := by
    have hh := prime_inv_log_square_tail (T.image (fun i => nthPrime i.val)) (by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
      exact nthPrime_prime i.val) J hJ hlJ (by
      intro p hp
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
      have hJi : J < i.val := by have := (mem_filter.mp hi).2; omega
      have hh := hJi.trans_le (nthPrime_strictMono.id_le i.val)
      exact_mod_cast hh)
    rw [sum_image (show Set.InjOn (fun i : Fin k => nthPrime i.val) T from
      (nthPrime_strictMono.injective.comp Fin.val_injective).injOn)] at hh
    exact hh
  have ht : (∑ i ∈ T, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val)) ≤
      splitTailCost J*D := by
    calc
      _ ≤ ∑ i ∈ T, (64*exp 4*D)*(1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) := by
        apply sum_le_sum
        intro i hi
        convert scaled_sharp_cost_le_log i.val _ (hchild i) using 1
        unfold primeMarginal
        ring
      _ = (64*exp 4*D)*(∑ i ∈ T, 1/((nthPrime i.val : ℝ)*log (nthPrime i.val)^2)) := by rw [mul_sum]
      _ ≤ (64*exp 4*D)*(inverseLogSquareConstant/log (J : ℝ)^2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by unfold splitTailCost; ring
  have he := sum_filter_add_sum_filter_not univ (fun i : Fin k => i.val ≤ J)
    (fun i => scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val))
  change (∑ i ∈ S, _)+(∑ i ∈ T, _) = _ at he
  rw [← he]
  exact add_le_add hs ht

lemma split_lower_zero (J k : ℕ) (hJ : 2 ≤ (J : ℝ)) (hlJ : 1 ≤ log (J : ℝ))
    (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0) k D ≤
      splitEarlyCost J+splitTailCost J*D := by
  classical
  change lowerErrorStep primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) k D ≤ _
  unfold lowerErrorStep
  split_ifs with hk
  · have hchild (i : Fin k) : (nthPrime i.val : ℝ) ≤ D*primeMarginal i.val := by
      have hp0 : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
      have hi : (nthPrime i.val : ℝ) ≤ nthPrime k := by exact_mod_cast (nthPrime_strictMono i.isLt).le
      have hki : (nthPrime k : ℝ)^2 ≤ D := hk
      change (nthPrime i.val : ℝ) ≤ D*(1/(nthPrime i.val : ℝ))
      rw [mul_one_div]
      apply (le_div_iff₀ hp0).mpr
      nlinarith only [hi,hki,hp0]
    have hs := split_child_sum J k hJ hlJ D hD hchild
    unfold splitEarlyCost
    linarith only [hs]
  · have hE := splitEarlyCost_ge J
    have hT := mul_nonneg (splitTailCost_nonneg J) hD
    linarith

lemma split_upper_one (J k K : ℕ) (hk : k ≤ K)
    (hJ : 2 ≤ (J : ℝ)) (hlJ : 1 ≤ log (J : ℝ)) (D : ℝ) (hD : 0 ≤ D) :
    upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1 k D ≤
      scaledSharpSelbergCost nthPrime k D+1+(k : ℝ)*splitEarlyCost J+
        splitTailCost J*D*prefixReciprocal nthPrime K := by
  classical
  change max (scaledSharpSelbergCost nthPrime k D)
    (1+∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0)
        i.val (D*primeMarginal i.val)) ≤ _
  have hE : 0 ≤ splitEarlyCost J := (by norm_num : (0 : ℝ) ≤ 1).trans (splitEarlyCost_ge J)
  have hT := splitTailCost_nonneg J
  have hZ := prefixReciprocal_nonneg nthPrime K
  apply max_le
  · have h1 : 0 ≤ (k : ℝ)*splitEarlyCost J := by positivity
    have h2 : 0 ≤ splitTailCost J*D*prefixReciprocal nthPrime K := by positivity
    linarith
  · have hs : (∑ i : Fin k, lowerErrorStep primeMarginal (primeKeep nthPrime)
        (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 0)
          i.val (D*primeMarginal i.val)) ≤
        (k : ℝ)*splitEarlyCost J+splitTailCost J*D*prefixReciprocal nthPrime K := by
      calc
        _ ≤ ∑ i : Fin k, (splitEarlyCost J+splitTailCost J*(D*primeMarginal i.val)) :=
          sum_le_sum (fun i _ => split_lower_zero J i.val hJ hlJ _ (mul_nonneg hD (primeMarginal_pos _).le))
        _ = (k : ℝ)*splitEarlyCost J+splitTailCost J*D*prefixReciprocal nthPrime k := by
          simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          congr 1
          dsimp only [prefixReciprocal,primeMarginal]
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          ring
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (prefixReciprocal_mono nthPrime hk) (by positivity))
    have hc := scaledSharpSelbergCost_nonneg nthPrime k D
    linarith only [hs,hc]

/-- Uniform in the actual prefix `k ≤ K`. All base and refined branch costs
are included. -/
theorem split_lower_one (J k K : ℕ) (hk : k ≤ K)
    (hJ : 2 ≤ (J : ℝ)) (hlJ : 1 ≤ log (J : ℝ)) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1) k D ≤
      splitEarlyCost J*(1+(K : ℝ)^2)+(K : ℝ)+
        splitTailCost J*D*(1+(prefixReciprocal nthPrime K)^2) := by
  classical
  have hE : 0 ≤ splitEarlyCost J := (by norm_num : (0 : ℝ) ≤ 1).trans (splitEarlyCost_ge J)
  have hT := splitTailCost_nonneg J
  have hZ := prefixReciprocal_nonneg nthPrime K
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
    have hsbase := split_child_sum J k hJ hlJ D hD hchild
    have hs : (∑ i : Fin k, upperError primeMarginal (primeKeep nthPrime)
        (scaledSharpSelbergCost nthPrime) 1 i.val (D*primeMarginal i.val)) ≤
        (∑ i : Fin k, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val))+
          (k : ℝ)+(k : ℝ)*(K : ℝ)*splitEarlyCost J+
          splitTailCost J*D*(prefixReciprocal nthPrime K)^2 := by
      calc
        _ ≤ ∑ i : Fin k, (scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val)+
            1+(K : ℝ)*splitEarlyCost J+splitTailCost J*(D*primeMarginal i.val)*prefixReciprocal nthPrime K) := by
          apply sum_le_sum
          intro i hi
          have hiK : i.val ≤ K := i.isLt.le.trans hk
          have hh := split_upper_one J i.val K hiK hJ hlJ (D*primeMarginal i.val) (mul_nonneg hD (primeMarginal_pos i.val).le)
          have hmul := mul_le_mul_of_nonneg_right (show (i.val : ℝ) ≤ K by exact_mod_cast hiK) hE
          linarith only [hh,hmul]
        _ = (∑ i : Fin k, scaledSharpSelbergCost nthPrime i.val (D*primeMarginal i.val))+
            (k : ℝ)+(k : ℝ)*(K : ℝ)*splitEarlyCost J+
            splitTailCost J*D*prefixReciprocal nthPrime k*prefixReciprocal nthPrime K := by
          simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [mul_assoc (k : ℝ)]
          congr 1
          dsimp only [prefixReciprocal,primeMarginal]
          rw [← sum_mul]
          congr 1
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left (prefixReciprocal_mono nthPrime hk)
            (show 0 ≤ splitTailCost J*D*prefixReciprocal nthPrime K by positivity)
          nlinarith only [hh]
    have hkR : (k : ℝ) ≤ K := by exact_mod_cast hk
    have hmul := mul_le_mul_of_nonneg_right hkR (show 0 ≤ (K : ℝ)*splitEarlyCost J by positivity)
    dsimp only [splitEarlyCost] at *
    nlinarith only [hs,hsbase,hkR,hmul]
  · positivity

#print axioms split_lower_one
end Erdos970.RecursiveSieve.Buchstab
