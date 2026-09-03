import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_329 : 3 ≤ primes 329 ∧ primes 329 ≤ 2503 ∧
    Row (primes 329) (states 329) (states 330) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
