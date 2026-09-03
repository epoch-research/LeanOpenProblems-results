import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_298 : 3 ≤ primes 298 ∧ primes 298 ≤ 2503 ∧
    Row (primes 298) (states 298) (states 299) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
