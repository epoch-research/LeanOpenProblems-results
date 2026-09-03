import Submission.FiveEvenBound

/-! An odd-order failure must have at least seven even-degree vertices. -/
namespace Erdos583FiveEvenFailureDevelopment
open SimpleGraph Erdos583Work Erdos583Work.ComponentDeficit
open Erdos583FiveEvenBoundDevelopment Erdos583UnifiedMinimalDefectDevelopment

lemma odd_failure_seven_even {V : Type*} [Fintype V] (G : SimpleGraph V)
    (ho : Odd (Fintype.card V))
    (hf : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card V : ℚ)/2⌉₊) : 7 ≤ evenCount G := by
  have hn : ¬evenCount G ≤ 5 := fun he ↦ hf (odd_order_at_most_five_even ho he)
  have hp := (odd_order_iff_evenCount_odd G).mp ho
  rw [Nat.odd_iff] at hp
  omega

lemma minimal_odd_failure_seven_even (F : MinimalFailure) (ho : Odd F.order) :
    7 ≤ evenCount F.graph :=
  odd_failure_seven_even F.graph (by simpa only [Fintype.card_fin] using ho) F.failure

end Erdos583FiveEvenFailureDevelopment
