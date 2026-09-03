import Submission.KernelNatQuotient

/-! Computable five-prime quarter-period certificate. The count formula is
transferred to actual phases in the companion proof; no external arithmetic
result is trusted by these finite checks. -/
namespace Erdos970.GapAverages.QuarterExample
open Finset

def positiveDivisors : List ℕ := [1, 21, 33, 57, 69, 77, 133, 161, 209, 253, 437, 4389, 5313, 9177, 14421, 33649]

def negativeDivisors : List ℕ := [3, 7, 11, 19, 23, 231, 399, 483, 627, 759, 1311, 1463, 1771, 3059, 4807, 100947]

def fastPrefix (x : ℕ) : ℤ :=
  (positiveDivisors.map (fun d => ((KernelArithmetic.quotient x d : ℕ) : ℤ))).sum -
    (negativeDivisors.map (fun d => ((KernelArithmetic.quotient x d : ℕ) : ℤ))).sum

def fastCount (m a : ℕ) : ℕ := (fastPrefix (a+m)-fastPrefix a).toNat

def blockWeight (m B b : ℕ) : ℕ :=
  ∑ a ∈ range 100, 2 ^ (B-fastCount m (100*b+a))

def weightedChunks (m B : ℕ) : ℕ :=
  (∑ b ∈ range 1009, blockWeight m B b) +
    ∑ a ∈ range 47, 2 ^ (B-fastCount m (100900+a))

end Erdos970.GapAverages.QuarterExample
