import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_282 : 3 ≤ primes 282 ∧ primes 282 ≤ 2503 ∧
    Row (primes 282) (states 282) (states 283) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
