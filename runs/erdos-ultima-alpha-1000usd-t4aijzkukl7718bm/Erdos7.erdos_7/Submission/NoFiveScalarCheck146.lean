import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_146 : 3 ≤ primes 146 ∧ primes 146 ≤ 2503 ∧
    Row (primes 146) (states 146) (states 147) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
