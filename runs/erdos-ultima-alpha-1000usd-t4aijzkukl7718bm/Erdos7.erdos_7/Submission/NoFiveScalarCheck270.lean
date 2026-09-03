import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_270 : 3 ≤ primes 270 ∧ primes 270 ≤ 2503 ∧
    Row (primes 270) (states 270) (states 271) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
