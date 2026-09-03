import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_220 : 3 ≤ primes 220 ∧ primes 220 ≤ 2503 ∧
    Row (primes 220) (states 220) (states 221) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
