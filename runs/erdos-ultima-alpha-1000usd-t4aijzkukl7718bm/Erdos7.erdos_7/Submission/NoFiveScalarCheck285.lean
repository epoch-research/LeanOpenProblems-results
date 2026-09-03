import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_285 : 3 ≤ primes 285 ∧ primes 285 ≤ 2503 ∧
    Row (primes 285) (states 285) (states 286) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
