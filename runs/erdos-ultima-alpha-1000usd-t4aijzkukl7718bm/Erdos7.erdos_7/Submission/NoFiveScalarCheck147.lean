import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_147 : 3 ≤ primes 147 ∧ primes 147 ≤ 2503 ∧
    Row (primes 147) (states 147) (states 148) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
