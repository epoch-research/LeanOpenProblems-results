import Submission.BuchstabSharpCost

/-! The inverse-log-square source saving at every fixed refinement depth. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg
set_option maxHeartbeats 0

lemma upperError_add (q : ℕ → ℝ) (keep : ℕ → ℝ → Prop)
    (cost : ℕ → ℝ → ℝ) (a b k : ℕ) (D : ℝ) :
    upperError q keep (upperError q keep cost a) b k D = upperError q keep cost (a+b) k D := by
  induction b generalizing k D with
  | zero => rfl
  | succ b ih =>
    have hf : upperError q keep (upperError q keep cost a) b = upperError q keep cost (a+b) :=
      funext (fun k => funext (fun D => ih k D))
    simp only [upperError,hf]
    rfl

lemma sharp_lower_depth_le_linear (n k K : ℕ) (hk : k ≤ K) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) (n+1)) k D ≤
      sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K)^(2*n+2)*D := by
  have hB : 1 ≤ sharpRefinementCostConstant := (by norm_num : (1 : ℝ) ≤ 4).trans sharpRefinementCostConstant_ge
  have hZ := prefixReciprocal_nonneg nthPrime K
  have hC : 1 ≤ sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K) :=
    one_le_mul_of_one_le_of_one_le hB (by linarith)
  have hh := refined_lowerError_le_linear_local primeMarginal (primeKeep nthPrime)
    (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1)
    (sharpRefinementCostConstant*(1+prefixReciprocal nthPrime K)) (prefixReciprocal nthPrime K)
    hC hZ (fun i => (primeMarginal_pos i).le) K
    (fun j hj => prefixReciprocal_mono nthPrime hj)
    (primeKeep_levels nthPrime nthPrime_prime nthPrime_strictMono)
    (fun j hj E hE => sharp_upper_one_le_linear j K hj E hE) n k hk D hD
  have hf : upperError primeMarginal (primeKeep nthPrime)
      (upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) 1) n =
      upperError primeMarginal (primeKeep nthPrime) (scaledSharpSelbergCost nthPrime) (n+1) := by
    funext j E
    rw [upperError_add, Nat.add_comm 1 n]
  rw [hf] at hh
  convert hh using 1
  rw [show 2*n+2=(2*n+1)+1 by omega,pow_succ]
  ring

#print axioms sharp_lower_depth_le_linear
end Erdos970.RecursiveSieve.Buchstab
