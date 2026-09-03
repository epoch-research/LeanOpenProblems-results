import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_284 : 3 ≤ primes 284 ∧ primes 284 ≤ 2503 ∧
    Row (primes 284) (states 284) (states 285) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
