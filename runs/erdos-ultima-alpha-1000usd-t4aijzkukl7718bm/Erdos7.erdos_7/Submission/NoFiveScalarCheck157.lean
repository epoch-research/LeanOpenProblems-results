import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_157 : 3 ≤ primes 157 ∧ primes 157 ≤ 2503 ∧
    Row (primes 157) (states 157) (states 158) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
