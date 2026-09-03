import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_115 : 3 ≤ primes 115 ∧ primes 115 ≤ 2503 ∧
    Row (primes 115) (states 115) (states 116) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
