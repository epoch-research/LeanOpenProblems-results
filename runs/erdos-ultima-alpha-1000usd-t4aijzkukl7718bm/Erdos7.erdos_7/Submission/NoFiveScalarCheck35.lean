import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_35 : 3 ≤ primes 35 ∧ primes 35 ≤ 2503 ∧
    Row (primes 35) (states 35) (states 36) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
