import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_255 : 3 ≤ primes 255 ∧ primes 255 ≤ 2503 ∧
    Row (primes 255) (states 255) (states 256) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
