import Submission.ThetaLower

/-! Stronger uniform second-moment bound, with a Chebyshev tail. -/
namespace Erdos7SharpRawBudget
open Erdos7No23Sieve Erdos7SharpRawPrefix
set_option maxHeartbeats 4000000

lemma prefix_budget_bound :
    budgetCost fixedPrimes.toFinset + (1/2 : ℚ)*budgetProduct fixedPrimes.toFinset/100000 < 419/500 := by
  have hL : ∀ p ∈ fixedPrimes, 5 ≤ p := fun p hp => ((mem_prefix p).mp hp).2.1
  have hd := roundedFold_dominates fixedPrimes hL (1000000,0) (1,0)
    (by norm_num [Dominates])
  change Dominates rounded (fixedPrimes.foldl rationalStep (1,0)) at hd
  rw [rounded_certificate,rationalFold_eq fixedPrimes prefix_pairwise 1 0] at hd
  simp only [Dominates,one_mul,zero_add] at hd
  norm_num at hd
  nlinarith [hd.1,hd.2]

/-- The finite fixedPrimes and the uniform tail bound cover every finite prime set. -/
theorem budgetCost_lt_419_500 (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) : budgetCost S < 419/500 := by
  let A := S.filter (· < 100000)
  let B := S.filter (fun p => ¬p < 100000)
  have hSAB : S = A ∪ B := (Finset.filter_union_filter_not_eq _ _).symm
  have hA : A ⊆ fixedPrimes.toFinset := by
    intro p hp
    obtain ⟨hp,hlo⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr ((mem_prefix p).mpr ⟨(hS p hp).1,(hS p hp).2,hlo⟩)
  have hB (p : ℕ) (hp : p ∈ B) : p.Prime ∧ 100000 ≤ p := by
    obtain ⟨hp,hhi⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hp).1,by omega⟩
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
    intro a ha b hb
    exact (Finset.mem_filter.mp ha).2.trans_le (hB b hb).2
  have hPA := budgetProduct_mono hA prefix_ge_five
  have hCA := budgetCost_mono hA prefix_ge_five
  have hCB := Erdos7ThetaLower.tail_cost_half B hB
  have hPA0 := budgetProduct_nonneg A (fun p hp => prefix_ge_five p (hA hp))
  have hterm : budgetProduct A * budgetCost B ≤
      budgetProduct fixedPrimes.toFinset * ((1/2 : ℚ)/100000) := by
    exact (mul_le_mul_of_nonneg_left hCB hPA0).trans
      (mul_le_mul_of_nonneg_right hPA (by norm_num))
  rw [hSAB,budgetCost_union hAB]
  apply (add_le_add hCA hterm).trans_lt
  convert prefix_budget_bound using 1 <;> ring

#print axioms budgetCost_lt_419_500
end Erdos7SharpRawBudget
