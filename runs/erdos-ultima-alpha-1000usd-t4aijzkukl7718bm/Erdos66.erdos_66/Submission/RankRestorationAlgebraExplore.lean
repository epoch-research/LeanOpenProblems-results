import Submission.RankRestorationSelectionExplore
import Submission.PredecessorCutoffTransferExplore

/-! Insertion after a deletion is charged once, against the original host. -/
namespace Erdos66RankRestorationAlgebra
open AdditiveCombinatorics Erdos66NatPairAlgebra Erdos66FiniteSwapAlgebra
  Erdos66AdaptiveSingletonAlgebra Erdos66PredecessorCutoffTransfer Erdos66Counting
  Erdos66OrderedPartialReplacement
open scoped Classical
set_option maxHeartbeats 2200000

lemma swapped_insertion_bound (A D F : Finset ℕ) (hF : Disjoint A F) (z : ℕ) :
    (sumRep (swapped A D F : Set ℕ) z : ℝ)-sumRep ((A\D : Finset ℕ) : Set ℕ) z ≤
      insertionEnergy A F z := by
  have hh := sumRep_swapped_upper (A\D) ∅ F (hF.mono_left Finset.sdiff_subset) z
  simp only [swapped,Finset.sdiff_empty] at hh
  have hp := pairs_mono_right (show A\D ⊆ A from Finset.sdiff_subset) (A := F) z
  have hh' : sumRep (swapped A D F : Set ℕ) z ≤
      sumRep ((A\D : Finset ℕ) : Set ℕ) z+2*pairs F A z+sumRep (F : Set ℕ) z := by
    dsimp only [swapped]
    omega
  have hhR : (sumRep (swapped A D F : Set ℕ) z : ℝ) ≤
      sumRep ((A\D : Finset ℕ) : Set ℕ) z+2*pairs F A z+sumRep (F : Set ℕ) z := by
    exact_mod_cast hh'
  dsimp only [insertionEnergy]
  linarith

lemma swapped_insertion_compare (A D F : Finset ℕ) (hF : Disjoint A F) (z : ℕ) :
    sumRep (swapped A D F : Set ℕ) z+sumRep (A : Set ℕ) z ≤
      sumRep ((A\D : Finset ℕ) : Set ℕ) z+sumRep ((A∪F : Finset ℕ) : Set ℕ) z := by
  have hh := swapped_insertion_bound A D F hF z
  rw [sumRep_union_self A F z hF,pairs_comm A F]
  dsimp only [insertionEnergy] at hh
  have he : (sumRep (swapped A D F : Set ℕ) z : ℝ)+sumRep (A : Set ℕ) z ≤
      sumRep ((A\D : Finset ℕ) : Set ℕ) z+
        (sumRep (A : Set ℕ) z+2*pairs F A z+sumRep (F : Set ℕ) z) := by linarith
  exact_mod_cast he

lemma swap_insertion_compare (A : Set ℕ) (D F : Finset ℕ)
    (hF : Disjoint (F : Set ℕ) A) (z : ℕ) :
    sumRep (swap A D F) z+sumRep A z ≤
      sumRep (A\(D : Set ℕ)) z+sumRep (A∪(F : Set ℕ)) z := by
  let B := cutoff A (z+1)
  have hBF : Disjoint B F := Finset.disjoint_left.mpr (fun a ha hf ↦
    Set.disjoint_left.mp hF hf (mem_cutoff.mp ha).2)
  have hh := swapped_insertion_compare B D F hBF z
  have hcore : sumRep ((B\D : Finset ℕ) : Set ℕ) z=sumRep (A\(D : Set ℕ)) z := by
    simpa only [swapped,Finset.union_empty,swap,Finset.coe_empty,Set.union_empty] using
      (cutoff_swap_rep A D ∅ (by omega : z<z+1))
  have hunion : sumRep ((B∪F : Finset ℕ) : Set ℕ) z=sumRep (A∪(F : Set ℕ)) z := by
    simpa only [swapped,Finset.sdiff_empty,swap,Finset.coe_empty,Set.diff_empty] using
      (cutoff_swap_rep A ∅ F (by omega : z<z+1))
  rw [cutoff_swap_rep A D F (by omega),cutoff_rep A (by omega),hcore,hunion] at hh
  exact hh

end Erdos66RankRestorationAlgebra
