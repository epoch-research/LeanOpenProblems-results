import FormalConjecturesUtil
import Submission.PrimeDiscrepancy

/-! A finite check ruling out nonnegativity of every signed prefix count.
This is not a disproof of the density conjecture. -/

namespace Erdos371SignedCountCheck

open Erdos371PrimeDiscrepancy

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma negative_signed_prefix : total 3895 = -1 := by
  decide +kernel

lemma not_always_nonnegative : ¬∀ N, 0 ≤ total N := by
  intro h
  have hh := h 3895
  rw [negative_signed_prefix] at hh
  omega

end Erdos371SignedCountCheck

#print axioms Erdos371SignedCountCheck.not_always_nonnegative
