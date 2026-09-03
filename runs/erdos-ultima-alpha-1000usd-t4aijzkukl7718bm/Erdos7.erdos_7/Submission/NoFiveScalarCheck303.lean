import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_303 : 3 ≤ primes 303 ∧ primes 303 ≤ 2503 ∧
    Row (primes 303) (states 303) (states 304) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
