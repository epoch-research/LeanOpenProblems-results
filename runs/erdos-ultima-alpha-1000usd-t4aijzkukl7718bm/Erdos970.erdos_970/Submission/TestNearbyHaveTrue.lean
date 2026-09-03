import Submission.NearbyCovarianceBlocks
/-! Development diagnostic. -/
open Finset
namespace Erdos970.GapAverages.NearbyExample
set_option maxHeartbeats 100000
set_option maxRecDepth 1000
lemma card_filter_range_blocks2 (p : ℕ → Prop) [DecidablePred p] (n m r : ℕ) :
    ((range (n*m+r)).filter p).card =
      (∑ b ∈ range m, ((range n).filter (fun a => p (n*b+a))).card) +
        ((range r).filter (fun a => p (n*m+a))).card := by
  rw [card_filter,sum_range_add,sum_blocks]
  simp only [sum_boole,Nat.cast_id]
#check @card_filter_range_blocks2
example : True := by
  have hc := card_filter_range_blocks2 (fun _ => True) 100 150 15
  trivial
end Erdos970.GapAverages.NearbyExample
