import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_53 : 3 ≤ primes 53 ∧ primes 53 ≤ 2503 ∧
    Row (primes 53) (states 53) (states 54) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
