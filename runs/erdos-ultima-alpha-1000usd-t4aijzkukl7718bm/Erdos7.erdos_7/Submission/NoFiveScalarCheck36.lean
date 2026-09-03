import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_36 : 3 ≤ primes 36 ∧ primes 36 ≤ 2503 ∧
    Row (primes 36) (states 36) (states 37) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
