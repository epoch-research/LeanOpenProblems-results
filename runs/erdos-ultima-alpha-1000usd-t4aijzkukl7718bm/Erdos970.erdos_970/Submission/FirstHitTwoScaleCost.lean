import Submission.FirstHitTwoScaleDefs

/-! Two-cutoff coefficient cost: O(exp(L)/L^2). This saves logarithmic
factors, not a positive power of the prime budget. -/
namespace Erdos970.FiniteSelberg
open Finset Real

lemma prime_inv_log_square_tail (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℝ) (ha : 2 ≤ a) (hla : 1 ≤ log a) (hlarge : ∀ p ∈ P, a < (p : ℝ)) :
    (∑ p ∈ P, 1/((p : ℝ)*log p^2)) ≤ inverseLogSquareConstant/log a^2 := by
  let b : ℝ := max a ((P.sup id : ℕ) : ℝ)
  let S := (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime
  have hab : a ≤ b := le_max_left _ _
  have hsub : P ⊆ S := by
    intro p hp
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (by linarith : 0 ≤ a)).mpr (hlarge p hp),?_⟩,hP p hp⟩
    exact Nat.le_floor ((show (p : ℝ) ≤ ((P.sup id : ℕ) : ℝ) by exact_mod_cast le_sup (f := id) hp).trans (le_max_right _ _))
  have hsum := sum_le_sum_of_subset_of_nonneg
    (f := fun p : ℕ => 1/((p : ℝ)*log p^2)) hsub (fun p _ _ => by positivity)
  have he := (abs_le.mp (WeightedMertens.abs_inverseLogPrimeInterval_sub 1 ha hab)).2
  norm_num only [Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] at he
  change (∑ p ∈ S, 1/((p : ℝ)*log p^2)) -
      (1/log a^2-1/log b^2)/2 ≤ 2*(WeightedMertens.boundConstant+1)/log a^3 at he
  have hB := WeightedMertens.boundConstant_pos
  have hlog : 0 < log a := by linarith
  have hpow : log a^2 ≤ log a^3 := by
    have hh := mul_nonneg (sq_nonneg (log a)) (show 0 ≤ log a-1 by linarith)
    nlinarith only [hh]
  have herr := div_le_div_of_nonneg_left
    (show 0 ≤ 2*(WeightedMertens.boundConstant+1) by positivity) (sq_pos_of_pos hlog) hpow
  have hz : 0 ≤ (1 : ℝ)/log b^2 := by positivity
  have hu : (∑ p ∈ P, 1/((p : ℝ)*log p^2)) ≤
      ((1/2 : ℝ)+2*(WeightedMertens.boundConstant+1))/log a^2 := by
    rw [add_div]
    have hid : ((1/2 : ℝ)/log a^2) = (1/log a^2)/2 := by ring
    rw [hid]
    linarith
  apply hu.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  unfold inverseLogSquareConstant
  linarith

lemma exp_half_le_exp_div_square (L : ℝ) (hL : 0 < L) :
    exp (L/2) ≤ 8*exp L/L^2 := by
  have h := quadratic_le_exp_of_nonneg (show 0 ≤ L/2 by positivity)
  have hh : L^2 ≤ 8*exp (L/2) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (exp_pos (L/2)).le
  have he : exp (L/2)*exp (L/2) = exp L := by rw [← exp_add]; congr 1; ring
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith only [hm,he]

noncomputable def twoScaleCostConstant : ℝ := 10008*normalizedFirstHitCostConstant
lemma twoScaleCostConstant_pos : 0 < twoScaleCostConstant :=
  mul_pos (by norm_num) normalizedFirstHitCostConstant_pos

/-- The actual reference squared costs, summed over every selected prime. -/
theorem twoScale_reference_cost (k : ℕ) (L : ℝ) (hL : 100 ≤ L)
    (hbound : ∀ i : Fin k, firstPrimeList k i ≤ saturatedHitPrimeCut L 0) :
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
      have hlog := (log_le_log hp0 (show (p i : ℝ) ≤ saturatedHitPrimeCut L 0 by
        exact_mod_cast hbound i)).trans (saturatedHit_top_log_bound L hLp.le).2
      have hz := reference_canonical_cost_at_scale k i L (by change 2*log (p i : ℝ) ≤ L; linarith)
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

#print axioms prime_inv_log_square_tail
#print axioms twoScale_reference_cost
end Erdos970.FiniteSelberg
