import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_361 : 3 ≤ primes 361 ∧ primes 361 ≤ 2503 ∧
    Row (primes 361) (states 361) (states 362) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
