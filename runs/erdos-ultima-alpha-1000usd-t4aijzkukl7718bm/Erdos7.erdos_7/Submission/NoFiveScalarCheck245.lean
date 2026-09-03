import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_245 : 3 ≤ primes 245 ∧ primes 245 ≤ 2503 ∧
    Row (primes 245) (states 245) (states 246) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
