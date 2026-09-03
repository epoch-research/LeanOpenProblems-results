import Submission.ArithmeticReduction

namespace Erdos7SharpRawPrefix
open Erdos7No23Sieve
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000

def primeRange (lo len : ℕ) : List ℕ := (List.range' lo len).filter (fun p =>
  decide (5 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p))

lemma primeRange_append (lo a b : ℕ) :
    primeRange lo (a+b) = primeRange lo a ++ primeRange (lo+a) b := by
  unfold primeRange
  rw [← List.range'_append_1, List.filter_append]

end Erdos7SharpRawPrefix
