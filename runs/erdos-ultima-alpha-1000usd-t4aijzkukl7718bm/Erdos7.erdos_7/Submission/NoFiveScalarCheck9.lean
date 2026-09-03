import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_9 : 3 ≤ primes 9 ∧ primes 9 ≤ 2503 ∧
    Row (primes 9) (states 9) (states 10) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
