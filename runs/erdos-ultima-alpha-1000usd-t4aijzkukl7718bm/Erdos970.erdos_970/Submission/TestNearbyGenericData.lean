import Submission.NearbyCovarianceBlocks
/-! Development diagnostic. -/
namespace Erdos970.GapAverages.NearbyExample
open Finset
lemma card_filter_range_blocks3 (p : ℕ → Prop) [DecidablePred p] (n m r : ℕ) :
    ((range (n*m+r)).filter p).card =
      (∑ b ∈ range m, ((range n).filter (fun a => p (n*b+a))).card) +
        ((range r).filter (fun a => p (n*m+a))).card := by
  rw [card_filter,sum_range_add,sum_blocks]
  simp only [sum_boole,Nat.cast_id]
end Erdos970.GapAverages.NearbyExample
