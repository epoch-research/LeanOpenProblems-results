import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_338 : 3 ≤ primes 338 ∧ primes 338 ≤ 2503 ∧
    Row (primes 338) (states 338) (states 339) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
