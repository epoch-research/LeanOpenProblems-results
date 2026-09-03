import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_332 : 3 ≤ primes 332 ∧ primes 332 ≤ 2503 ∧
    Row (primes 332) (states 332) (states 333) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
