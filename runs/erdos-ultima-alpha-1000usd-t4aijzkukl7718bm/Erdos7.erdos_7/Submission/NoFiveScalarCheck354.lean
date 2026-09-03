import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_354 : 3 ≤ primes 354 ∧ primes 354 ≤ 2503 ∧
    Row (primes 354) (states 354) (states 355) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
