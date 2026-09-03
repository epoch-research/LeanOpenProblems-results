import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_323 : 3 ≤ primes 323 ∧ primes 323 ≤ 2503 ∧
    Row (primes 323) (states 323) (states 324) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
