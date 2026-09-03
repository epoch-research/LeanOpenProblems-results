import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_172 : 3 ≤ primes 172 ∧ primes 172 ≤ 2503 ∧
    Row (primes 172) (states 172) (states 173) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
