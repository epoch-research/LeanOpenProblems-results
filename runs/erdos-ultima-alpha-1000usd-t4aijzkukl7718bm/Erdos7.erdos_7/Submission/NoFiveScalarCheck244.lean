import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_244 : 3 ≤ primes 244 ∧ primes 244 ≤ 2503 ∧
    Row (primes 244) (states 244) (states 245) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
