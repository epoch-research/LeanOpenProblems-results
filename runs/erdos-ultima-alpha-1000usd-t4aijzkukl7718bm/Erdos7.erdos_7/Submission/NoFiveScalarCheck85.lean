import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_85 : 3 ≤ primes 85 ∧ primes 85 ≤ 2503 ∧
    Row (primes 85) (states 85) (states 86) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
