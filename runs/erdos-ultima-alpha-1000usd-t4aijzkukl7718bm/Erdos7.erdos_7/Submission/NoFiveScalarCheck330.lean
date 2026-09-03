import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_330 : 3 ≤ primes 330 ∧ primes 330 ≤ 2503 ∧
    Row (primes 330) (states 330) (states 331) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
