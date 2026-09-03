import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_126 : 3 ≤ primes 126 ∧ primes 126 ≤ 2503 ∧
    Row (primes 126) (states 126) (states 127) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
