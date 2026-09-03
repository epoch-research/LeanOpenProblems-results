import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_58 : 3 ≤ primes 58 ∧ primes 58 ≤ 2503 ∧
    Row (primes 58) (states 58) (states 59) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
