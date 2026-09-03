import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_237 : 3 ≤ primes 237 ∧ primes 237 ≤ 2503 ∧
    Row (primes 237) (states 237) (states 238) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
