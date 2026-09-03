import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_87 : 3 ≤ primes 87 ∧ primes 87 ≤ 2503 ∧
    Row (primes 87) (states 87) (states 88) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
