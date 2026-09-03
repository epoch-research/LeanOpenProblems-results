import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_265 : 3 ≤ primes 265 ∧ primes 265 ≤ 2503 ∧
    Row (primes 265) (states 265) (states 266) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
