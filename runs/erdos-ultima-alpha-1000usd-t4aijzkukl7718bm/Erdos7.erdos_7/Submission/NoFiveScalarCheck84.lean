import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_84 : 3 ≤ primes 84 ∧ primes 84 ≤ 2503 ∧
    Row (primes 84) (states 84) (states 85) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
