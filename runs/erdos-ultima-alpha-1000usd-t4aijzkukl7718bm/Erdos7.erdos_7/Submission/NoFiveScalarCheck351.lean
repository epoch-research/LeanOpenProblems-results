import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_351 : 3 ≤ primes 351 ∧ primes 351 ≤ 2503 ∧
    Row (primes 351) (states 351) (states 352) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
