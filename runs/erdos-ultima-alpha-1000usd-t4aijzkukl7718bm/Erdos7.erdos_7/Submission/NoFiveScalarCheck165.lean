import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_165 : 3 ≤ primes 165 ∧ primes 165 ≤ 2503 ∧
    Row (primes 165) (states 165) (states 166) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
