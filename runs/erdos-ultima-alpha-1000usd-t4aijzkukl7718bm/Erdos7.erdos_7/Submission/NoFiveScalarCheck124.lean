import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_124 : 3 ≤ primes 124 ∧ primes 124 ≤ 2503 ∧
    Row (primes 124) (states 124) (states 125) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
