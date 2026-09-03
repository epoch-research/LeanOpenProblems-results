import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_268 : 3 ≤ primes 268 ∧ primes 268 ≤ 2503 ∧
    Row (primes 268) (states 268) (states 269) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
