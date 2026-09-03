import Submission.NearbyCovarianceBlocks

/-! Assembly of independently kernel-checked finite cover counts. -/
namespace Erdos970.GapAverages.NearbyExample
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option Elab.async false

lemma card_filter_range_blocks (p : ℕ → Prop) [DecidablePred p] (n m r : ℕ) :
    ((range (n*m+r)).filter p).card =
      (∑ b ∈ range m, ((range n).filter (fun a => p (n*b+a))).card) +
        ((range r).filter (fun a => p (n*m+a))).card := by
  rw [card_filter,sum_range_add,sum_blocks]
  simp only [sum_boole,Nat.cast_id]

lemma cover_count_certificate :
    ((range 15015).filter (fun a => CyclicSieve.natCount primes 7 a = 0)).card = 36 := by
  classical
  have hc := card_filter_range_blocks (fun a => CyclicSieve.natCount primes 7 a = 0) 100 150 15
  change ((range 15015).filter (fun a => CyclicSieve.natCount primes 7 a = 0)).card = _ at hc
  rw [hc]
  change (∑ b ∈ range 150, blockCount b) + _ = 36
  rw [last_block]
  fail "STOP6"
end Erdos970.GapAverages.NearbyExample
