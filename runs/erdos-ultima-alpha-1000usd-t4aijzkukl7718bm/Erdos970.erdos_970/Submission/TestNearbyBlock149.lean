import Submission.CyclicSieveCount

/-! A finite, kernel-checked cover-count certificate for five odd primes.
The count is split into short blocks to bound kernel reduction memory. -/
namespace Erdos970.GapAverages.NearbyExample
open Finset ParityDiscrepancy
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def primes : Finset ℕ := {3,5,7,11,13}

lemma primes_prime : ∀ p ∈ primes, p.Prime := by norm_num [primes]
lemma prime_product : primeProduct primes = 15015 := by norm_num [primeProduct,primes]

def blockCount (b : ℕ) : ℕ :=
  ((range 100).filter (fun a => CyclicSieve.natCount primes 7 (100*b+a) = 0)).card

lemma block_149 : blockCount 149 = 1 := by decide +kernel
#print axioms block_149
end Erdos970.GapAverages.NearbyExample
