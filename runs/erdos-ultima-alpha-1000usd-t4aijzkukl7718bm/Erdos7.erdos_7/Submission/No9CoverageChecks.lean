import Submission.No9CoverageData

/-! Boolean obligations certifying candidate coverage of all small primes. -/
namespace Erdos7No9Certificate
open Erdos7PrimeCoverage
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

def prefixPrimeCoverageCheck : Bool :=
  coverageCheck 3 (5000-3) prefixLength (fun j => (prefixControl j).p) prefixWitness

def blockPrimeCoverageCheck (i : ℕ) : Bool :=
  let b := blockControl i
  decide (b.lo < b.hi) && coverageCheck b.lo (b.hi-b.lo) b.count (blockCandidate i) (blockWitness i) &&
    orderCheck b.lo b.hi b.count (blockCandidate i)

end Erdos7No9Certificate
