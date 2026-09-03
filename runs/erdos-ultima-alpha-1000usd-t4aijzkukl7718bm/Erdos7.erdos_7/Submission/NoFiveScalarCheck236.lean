import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_236 : 3 ≤ primes 236 ∧ primes 236 ≤ 2503 ∧
    Row (primes 236) (states 236) (states 237) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
