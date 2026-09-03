import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_261 : 3 ≤ primes 261 ∧ primes 261 ≤ 2503 ∧
    Row (primes 261) (states 261) (states 262) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
