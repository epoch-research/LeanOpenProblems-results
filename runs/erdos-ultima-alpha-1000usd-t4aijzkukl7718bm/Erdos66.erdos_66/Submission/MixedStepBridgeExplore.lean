import Submission.MixedPaletteAssemblyExplore
import Submission.StepConvolutionBridgeExplore

/-! Exact mixed convolution bridge for two different finite step profiles. -/
namespace Erdos66MixedStepBridge
open Erdos66StepConvolutionBridge Erdos66MixedPaletteAssembly Erdos66IntegerPaletteQuantization
  Erdos66NatPairAlgebra Erdos66IntegerPaletteSlices
open scoped Classical
set_option maxHeartbeats 2600000

noncomputable def normMixedConv (M : ℕ) (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ x∈Finset.range M, if x ≤ n ∧ n-x<M then f x*g (n-x) else 0)/M

lemma normMixedConv_self (M : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    normMixedConv M f f n=normConv M f n := rfl

theorem mixedProfile_eq_normMixedConv (M : ℕ) [NeZero M] {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b d e : ι → ℕ) (hb : ∀ i∈s, b i ≤ M) (he : ∀ i∈s, e i ≤ M) (n : ℕ) :
    mixedProfile M s w a b d e n = normMixedConv M (stepFunction s w a b) (stepFunction s w d e) n := by
  have hover (i : ι) (hi : i∈s) (j : ι) (hj : j∈s) :
      overlap M (a i) (b i) (d j) (e j) n =
        (pairs (Finset.Ico (a i) (b i)) (Finset.Ico (d j) (e j)) n:ℝ)/M := by
    rw [pairs_Ico,Nat.cast_sub (cutLo_le_cutHi _ _ _ _ _)]
    rfl
  have hw : mixedProfile M s w a b d e n =
      (∑ i∈s, ∑ j∈s, (pairs (Finset.Ico (a i) (b i)) (Finset.Ico (d j) (e j)) n:ℝ)*(w i*w j))/M := by
    simp only [mixedProfile,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hover i hi j hj]
    ring
  rw [hw,normMixedConv]
  congr 1
  calc
    _ = ∑ i∈s, ∑ j∈s, ∑ x∈Finset.range M,
        if a i ≤ x ∧ x<b i ∧ x ≤ n ∧ d j ≤ n-x ∧ n-x<e j then w i*w j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [pairs_Ico_sum M _ _ _ _ _ (hb i hi),Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> ring
    _ = ∑ x∈Finset.range M, ∑ i∈s, ∑ j∈s,
        if a i ≤ x ∧ x<b i ∧ x ≤ n ∧ d j ≤ n-x ∧ n-x<e j then w i*w j else 0 := by
      simp_rw [Finset.sum_comm (s:=s) (t:=Finset.range M)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hn : x ≤ n ∧ n-x<M
      · simp only [if_pos hn,stepFunction,Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [indicator_step_product]
        have he : (a i ≤ x ∧ x<b i ∧ x ≤ n ∧ d j ≤ n-x ∧ n-x<e j) ↔
            (a i ≤ x ∧ x<b i) ∧ (d j ≤ n-x ∧ n-x<e j) := by omega
        simp only [he]
      · simp only [if_neg hn]
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        have hnot : ¬(a i ≤ x ∧ x<b i ∧ x ≤ n ∧ d j ≤ n-x ∧ n-x<e j) := by
          intro hh
          exact hn ⟨hh.2.2.1,hh.2.2.2.2.trans_le (he j hj)⟩
        simp only [if_neg hnot]


end Erdos66MixedStepBridge
