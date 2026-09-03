import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_246 : 3 ≤ primes 246 ∧ primes 246 ≤ 2503 ∧
    Row (primes 246) (states 246) (states 247) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
