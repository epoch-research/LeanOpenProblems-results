import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_164 : 3 ≤ primes 164 ∧ primes 164 ≤ 2503 ∧
    Row (primes 164) (states 164) (states 165) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
