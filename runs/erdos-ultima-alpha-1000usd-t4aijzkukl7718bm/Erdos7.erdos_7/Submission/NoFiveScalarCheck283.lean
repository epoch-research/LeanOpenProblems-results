import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_283 : 3 ≤ primes 283 ∧ primes 283 ≤ 2503 ∧
    Row (primes 283) (states 283) (states 284) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
