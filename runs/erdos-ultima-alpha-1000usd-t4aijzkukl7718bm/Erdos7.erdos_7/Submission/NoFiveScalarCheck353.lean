import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_353 : 3 ≤ primes 353 ∧ primes 353 ≤ 2503 ∧
    Row (primes 353) (states 353) (states 354) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
