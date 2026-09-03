import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_305 : 3 ≤ primes 305 ∧ primes 305 ≤ 2503 ∧
    Row (primes 305) (states 305) (states 306) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
