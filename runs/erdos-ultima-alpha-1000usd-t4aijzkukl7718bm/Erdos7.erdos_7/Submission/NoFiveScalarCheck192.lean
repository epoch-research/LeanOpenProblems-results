import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_192 : 3 ≤ primes 192 ∧ primes 192 ≤ 2503 ∧
    Row (primes 192) (states 192) (states 193) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
