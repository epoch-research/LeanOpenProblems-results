import Submission.FirstHitTwoScaleCost

/-! The same cost estimate applies whenever all selected reference primes are
at most exp(L/2). No narrower endpoint assumption is needed. -/
namespace Erdos970.FiniteSelberg
open Finset Real

theorem twoScale_reference_cost_of_log_bound (k : ℕ) (L : ℝ) (hL : 100 ≤ L)
    (hbound : ∀ i : Fin k, 2*log (firstPrimeList k i : ℝ) ≤ L) :
    (∑ i : Fin k, kernelCost (fun j => 1/(firstPrimeList k j : ℝ))
      (canonicalOrthogonal (fun j => 1/(firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (twoScaleCutoff L (firstPrimeList k i))))^2) ≤
      twoScaleCostConstant * exp L/L^2 := by
  let p := firstPrimeList k
  let q := fun j => 1/(p j : ℝ)
  let f := fun i => kernelCost q (canonicalOrthogonal q
    (priorDivisorSupport p i (twoScaleCutoff L (p i))))^2
  let S : Finset (Fin k) := univ.filter (fun i => log (p i : ℝ) ≤ L/100)
  let T : Finset (Fin k) := univ.filter (fun i => ¬log (p i : ℝ) ≤ L/100)
  have hLp : 0 < L := by linarith
  have hp := firstPrimeList_prime k
  have hinj := (firstPrimeList_strictMono k).injective
  have hsumS : (∑ i ∈ S, 1/((p i : ℝ)*log (p i)^2)) ≤ inverseLogSquareConstant := by
    have hh := prime_inv_log_square_sum_le (S.image p) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact hp i)
    rwa [sum_image hinj.injOn] at hh
  have hsumT : (∑ i ∈ T, 1/((p i : ℝ)*log (p i)^2)) ≤
      10000*inverseLogSquareConstant/L^2 := by
    have ha : 2 ≤ exp (L/100) := by linarith [add_one_le_exp (L/100)]
    have hla : 1 ≤ log (exp (L/100)) := by rw [log_exp]; linarith
    have hh := prime_inv_log_square_tail (T.image p) (by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      exact hp i) (exp (L/100)) ha hla (by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      have hi' := (mem_filter.mp hi).2
      have hpi : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      rw [← exp_log hpi]
      exact exp_lt_exp.mpr (by linarith))
    rw [sum_image hinj.injOn,log_exp] at hh
    convert hh using 1 <;> ring
  have hs : (∑ i ∈ S, f i) ≤ normalizedFirstHitCostConstant*exp (L/2) := by
    have ht (i : Fin k) (hi : i ∈ S) : f i ≤
        (64*exp 4*exp (L/2))*(1/((p i : ℝ)*log (p i)^2)) := by
      have hi' := (mem_filter.mp hi).2
      have hh := reference_canonical_cost_at_scale k i (L/2) (by change 2*log (p i : ℝ) ≤ L/2; linarith)
      simpa only [f,q,p,twoScaleCutoff,twoScaleParameter,if_pos hi'] using hh
    have hh := sum_le_sum ht
    rw [← mul_sum] at hh
    have hm := mul_le_mul_of_nonneg_left hsumS (show 0 ≤ 64*exp 4*exp (L/2) by positivity)
    exact hh.trans (by simpa only [normalizedFirstHitCostConstant,mul_assoc,mul_comm,mul_left_comm] using hm)
  have ht : (∑ i ∈ T, f i) ≤ 10000*normalizedFirstHitCostConstant*exp L/L^2 := by
    have hh (i : Fin k) (hi : i ∈ T) : f i ≤
        (64*exp 4*exp L)*(1/((p i : ℝ)*log (p i)^2)) := by
      have hi' := (mem_filter.mp hi).2
      have hp0 : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
      have hz := reference_canonical_cost_at_scale k i L (hbound i)
      simpa only [f,q,p,twoScaleCutoff,twoScaleParameter,if_neg hi'] using hz
    have hz := sum_le_sum hh
    rw [← mul_sum] at hz
    have hm := mul_le_mul_of_nonneg_left hsumT (show 0 ≤ 64*exp 4*exp L by positivity)
    exact hz.trans (by convert hm using 1 <;> dsimp [normalizedFirstHitCostConstant]; ring)
  have hf := sum_filter_add_sum_filter_not univ (fun i => log (p i : ℝ) ≤ L/100) f
  change (∑ i ∈ S, f i)+(∑ i ∈ T, f i) = ∑ i, f i at hf
  have he := mul_le_mul_of_nonneg_left (exp_half_le_exp_div_square L hLp)
    normalizedFirstHitCostConstant_pos.le
  change (∑ i, f i) ≤ _
  rw [← hf]
  unfold twoScaleCostConstant
  calc
    _ ≤ normalizedFirstHitCostConstant*exp (L/2)+
        10000*normalizedFirstHitCostConstant*exp L/L^2 := add_le_add hs ht
    _ ≤ normalizedFirstHitCostConstant*(8*exp L/L^2)+
        10000*normalizedFirstHitCostConstant*exp L/L^2 := add_le_add he le_rfl
    _ = _ := by ring

#print axioms twoScale_reference_cost_of_log_bound
end Erdos970.FiniteSelberg
