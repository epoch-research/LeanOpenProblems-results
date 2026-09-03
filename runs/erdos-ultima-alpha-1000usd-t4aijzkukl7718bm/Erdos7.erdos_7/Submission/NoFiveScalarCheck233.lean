import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_233 : 3 ≤ primes 233 ∧ primes 233 ≤ 2503 ∧
    Row (primes 233) (states 233) (states 234) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
