import Submission.SupportPrefixMetadata

/-! Finite prime-table checks for the auxiliary support sieve. -/
namespace Erdos7SupportPrimeMetadata
open Erdos7SupportPrefixMetadata Erdos7SupportPrefixData
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
local instance : DecidablePred Nat.Prime := Nat.decidablePrime'

theorem prefix_primes : ∀ i : Fin 167,(p i).Prime ∧ p i < 1000 := by decide +kernel

theorem prefix_gaps : ∀ i : Fin 166,p i+2 ≤ p (i.val+1) := by decide +kernel

theorem prefix_covers : ∀ q : Fin 1001,q.val.Prime → q.val≠2 → ∃ i : Fin 167,p i=q.val := by decide +kernel

#print axioms prefix_primes
#print axioms prefix_gaps
#print axioms prefix_covers
end Erdos7SupportPrimeMetadata
