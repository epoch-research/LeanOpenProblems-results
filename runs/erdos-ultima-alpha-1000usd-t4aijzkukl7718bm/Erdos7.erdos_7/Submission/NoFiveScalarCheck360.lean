import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_360 : 3 ≤ primes 360 ∧ primes 360 ≤ 2503 ∧
    Row (primes 360) (states 360) (states 361) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
