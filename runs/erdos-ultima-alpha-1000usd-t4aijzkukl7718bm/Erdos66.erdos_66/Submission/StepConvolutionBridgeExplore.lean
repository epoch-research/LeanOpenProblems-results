import Submission.IntegerPaletteQuantizationExplore

/-! The geometric overlap profile is exactly the discrete convolution of its
step function. This identifies the target of the finite palette construction. -/
namespace Erdos66StepConvolutionBridge
open Erdos66NatPairAlgebra Erdos66IntegerPaletteSlices Erdos66IntegerPaletteQuantization
open scoped Classical
set_option maxHeartbeats 2400000

lemma pairs_Ico (a b c d n : ℕ) :
    pairs (Finset.Ico a b) (Finset.Ico c d) n = cutHi b c n-cutLo a b c d n := by
  rw [pairs_eq_filter]
  have he : (Finset.Ico a b).filter (fun x ↦ x ≤ n ∧ n-x∈Finset.Ico c d) =
      Finset.Ico (cutLo a b c d n) (cutHi b c n) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_Ico]
    rw [cut_bounds_iff]
    tauto
  rw [he]
  simp

noncomputable def normConv (M : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ x∈Finset.range M, if x ≤ n ∧ n-x<M then f x*f (n-x) else 0)/M

noncomputable def stepFunction {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (a b : ι → ℕ) (x : ℕ) : ℝ := ∑ i∈s, if a i ≤ x ∧ x<b i then w i else 0

lemma pairs_Ico_sum (M a b c d n : ℕ) (hb : b ≤ M) :
    (pairs (Finset.Ico a b) (Finset.Ico c d) n:ℝ) =
      ∑ x∈Finset.range M, if a ≤ x ∧ x<b ∧ x ≤ n ∧ c ≤ n-x ∧ n-x<d then 1 else 0 := by
  have he : (Finset.Ico a b).filter (fun x ↦ x ≤ n ∧ n-x∈Finset.Ico c d) =
      (Finset.range M).filter (fun x ↦ a ≤ x ∧ x<b ∧ x ≤ n ∧ c ≤ n-x ∧ n-x<d) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [pairs_eq_filter,he,Finset.card_filter]
  push_cast
  rfl

lemma indicator_step_product (A B : Prop) [Decidable A] [Decidable B] (u v : ℝ) :
    (if A then u else 0)*(if B then v else 0) = if A ∧ B then u*v else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA,hB]

/-- No disjointness is required for this algebraic identity: overlapping steps
are added in the fractional profile. -/
theorem weightedProfile_eq_normConv (M : ℕ) [NeZero M] {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (a b : ι → ℕ) (hb : ∀ i∈s, b i ≤ M) (n : ℕ) :
    weightedProfile M s w a b n = normConv M (stepFunction s w a b) n := by
  have hover (i : ι) (hi : i∈s) (j : ι) (hj : j∈s) :
      overlap M (a i) (b i) (a j) (b j) n =
        (pairs (Finset.Ico (a i) (b i)) (Finset.Ico (a j) (b j)) n:ℝ)/M := by
    rw [pairs_Ico,Nat.cast_sub (cutLo_le_cutHi _ _ _ _ _)]
    rfl
  have hw : weightedProfile M s w a b n =
      (∑ i∈s, ∑ j∈s, (pairs (Finset.Ico (a i) (b i)) (Finset.Ico (a j) (b j)) n:ℝ)*(w i*w j))/M := by
    simp only [weightedProfile,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hover i hi j hj]
    ring
  rw [hw,normConv]
  congr 1
  calc
    _ = ∑ i∈s, ∑ j∈s, ∑ x∈Finset.range M,
        if a i ≤ x ∧ x<b i ∧ x ≤ n ∧ a j ≤ n-x ∧ n-x<b j then w i*w j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [pairs_Ico_sum M _ _ _ _ _ (hb i hi),Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> ring
    _ = ∑ x∈Finset.range M, ∑ i∈s, ∑ j∈s,
        if a i ≤ x ∧ x<b i ∧ x ≤ n ∧ a j ≤ n-x ∧ n-x<b j then w i*w j else 0 := by
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
        have he : (a i ≤ x ∧ x<b i ∧ x ≤ n ∧ a j ≤ n-x ∧ n-x<b j) ↔
            (a i ≤ x ∧ x<b i) ∧ (a j ≤ n-x ∧ n-x<b j) := by omega
        simp only [he]
      · simp only [if_neg hn]
        apply Finset.sum_eq_zero
        intro i hi
        apply Finset.sum_eq_zero
        intro j hj
        have hnot : ¬(a i ≤ x ∧ x<b i ∧ x ≤ n ∧ a j ≤ n-x ∧ n-x<b j) := by
          intro hh
          exact hn ⟨hh.2.2.1,hh.2.2.2.2.trans_le (hb j hj)⟩
        simp only [if_neg hnot]

end Erdos66StepConvolutionBridge
