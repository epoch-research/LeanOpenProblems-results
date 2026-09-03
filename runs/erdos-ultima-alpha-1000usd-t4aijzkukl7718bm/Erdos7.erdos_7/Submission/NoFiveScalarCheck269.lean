import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_269 : 3 ≤ primes 269 ∧ primes 269 ≤ 2503 ∧
    Row (primes 269) (states 269) (states 270) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
