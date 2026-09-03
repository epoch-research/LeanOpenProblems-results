import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_253 : 3 ≤ primes 253 ∧ primes 253 ≤ 2503 ∧
    Row (primes 253) (states 253) (states 254) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
