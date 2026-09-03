import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_256 : 3 ≤ primes 256 ∧ primes 256 ≤ 2503 ∧
    Row (primes 256) (states 256) (states 257) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
