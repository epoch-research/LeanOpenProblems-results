import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_352 : 3 ≤ primes 352 ∧ primes 352 ≤ 2503 ∧
    Row (primes 352) (states 352) (states 353) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
