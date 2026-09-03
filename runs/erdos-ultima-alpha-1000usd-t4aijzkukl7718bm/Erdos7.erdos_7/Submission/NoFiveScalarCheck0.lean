import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_0 : 3 ≤ primes 0 ∧ primes 0 ≤ 2503 ∧
    Row (primes 0) (states 0) (states 1) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
