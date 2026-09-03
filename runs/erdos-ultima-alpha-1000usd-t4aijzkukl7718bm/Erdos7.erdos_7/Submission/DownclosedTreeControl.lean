import Submission.SplittingTreeCover
/-! An EVEN positive control for divisor-closed construction search. -/
namespace Erdos7DownclosedTreeControl
open Erdos7SplittingTreeCover
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
def candidate : Tree := .split 2 ![.leaf 2,.split 3 ![.leaf 6,.leaf 3,.split 2 ![.leaf 12,.leaf 4]]]
lemma candidate_valid : candidate.Valid 1 := by decide +kernel
lemma candidate_injective : Function.Injective candidate.modulus := by decide +kernel
lemma candidate_covers : ∀ x : ℤ, ∃ k : candidate.Leaf,
    (candidate.modulus k : ℤ) ∣ x-candidate.residue 1 0 k := by
  intro x
  exact candidate.covers 1 0 candidate_valid x (by simp)
#print axioms candidate_valid
#print axioms candidate_injective
#print axioms candidate_covers
end Erdos7DownclosedTreeControl
