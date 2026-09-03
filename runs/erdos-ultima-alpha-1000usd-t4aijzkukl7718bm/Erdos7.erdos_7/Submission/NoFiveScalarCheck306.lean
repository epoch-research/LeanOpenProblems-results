import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_306 : 3 ≤ primes 306 ∧ primes 306 ≤ 2503 ∧
    Row (primes 306) (states 306) (states 307) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
