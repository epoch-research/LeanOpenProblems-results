import Submission.InsertionMatchingPatternExplore
import Submission.PredecessorCutoffTransferExplore
import Submission.InfiniteLogApproximationExplore

/-! Monotonicity of a disjoint insertion increment in its old host, and a
zero-limit transfer from shifted to unshifted logarithms. -/
namespace Erdos66InsertionIncrementComparison
open Filter AdditiveCombinatorics Erdos66Generating Erdos66Rounding
  Erdos66Explore Erdos66InfiniteLogApproximation
open scoped Classical Topology
set_option maxHeartbeats 2800000

lemma indicator_union_disjoint (A F : Set ℕ) (h : Disjoint A F) :
    indicator (A∪F)=fun i ↦ indicator A i+indicator F i := by
  funext i
  by_cases hiA : i∈A <;> by_cases hiF : i∈F
  · exact False.elim (Set.disjoint_left.mp h hiA hiF)
  all_goals simp [indicator,hiA,hiF]

lemma disjoint_union_rep (A F : Set ℕ) (h : Disjoint A F) (n : ℕ) :
    (sumRep (A∪F) n : ℝ)=(sumRep A n : ℝ)+2*sumConv (indicator A) (indicator F) n+(sumRep F n : ℝ) := by
  rw [←sum_indicator_antidiagonal (A∪F) n]
  change sumConv (indicator (A∪F)) (indicator (A∪F)) n=_
  rw [indicator_union_disjoint A F h,sumConv_add_self]
  rw [show sumConv (indicator A) (indicator A) n=(sumRep A n : ℝ) from sum_indicator_antidiagonal A n,
    show sumConv (indicator F) (indicator F) n=(sumRep F n : ℝ) from sum_indicator_antidiagonal F n]

lemma insertion_increment_mono (H A F : Set ℕ) (hHA : H ⊆ A) (hFA : Disjoint F A) (n : ℕ) :
    (sumRep (H∪F) n : ℝ)-(sumRep H n : ℝ) ≤
      (sumRep (A∪F) n : ℝ)-(sumRep A n : ℝ) := by
  have hHF : Disjoint H F := hFA.symm.mono_left hHA
  rw [disjoint_union_rep H F hHF,disjoint_union_rep A F hFA.symm]
  have hi (i : ℕ) : indicator H i ≤ indicator A i := by
    by_cases hH : i∈H
    · simp [indicator,hH,hHA hH]
    · simp only [indicator,hH,if_false]
      split_ifs <;> norm_num
  have hm : sumConv (indicator H) (indicator F) n ≤ sumConv (indicator A) (indicator F) n :=
    Finset.sum_le_sum (fun ij _ ↦ mul_le_mul_of_nonneg_right (hi _) (indicator_nonneg F _))
  linarith

lemma log_zero_unshift (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (h : Tendsto (fun n : ℕ ↦ f n/Real.log ((n : ℝ)+2)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ f n/Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hh := h.const_mul 2
  simp only [mul_zero] at hh
  apply squeeze_zero' ?_ ?_ hh
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (hf n) (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hL : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<n by omega))
    have hL' : 0<Real.log ((n : ℝ)+2) := Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    have hb := mul_le_mul_of_nonneg_left (log_shift_bound n hn) (hf n)
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hL hL').mpr
    nlinarith only [hb]

end Erdos66InsertionIncrementComparison
