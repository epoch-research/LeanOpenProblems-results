import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_314 : 3 ≤ primes 314 ∧ primes 314 ≤ 2503 ∧
    Row (primes 314) (states 314) (states 315) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
