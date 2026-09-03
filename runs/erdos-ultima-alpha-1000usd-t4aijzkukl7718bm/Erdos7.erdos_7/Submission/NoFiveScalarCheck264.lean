import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_264 : 3 ≤ primes 264 ∧ primes 264 ≤ 2503 ∧
    Row (primes 264) (states 264) (states 265) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
