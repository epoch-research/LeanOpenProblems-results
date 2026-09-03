import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_108 : 3 ≤ primes 108 ∧ primes 108 ≤ 2503 ∧
    Row (primes 108) (states 108) (states 109) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
