import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_221 : 3 ≤ primes 221 ∧ primes 221 ≤ 2503 ∧
    Row (primes 221) (states 221) (states 222) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
