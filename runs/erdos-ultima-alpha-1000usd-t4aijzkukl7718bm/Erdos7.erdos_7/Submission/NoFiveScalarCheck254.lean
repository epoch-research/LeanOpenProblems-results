import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_254 : 3 ≤ primes 254 ∧ primes 254 ≤ 2503 ∧
    Row (primes 254) (states 254) (states 255) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
