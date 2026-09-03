import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_72 : 3 ≤ primes 72 ∧ primes 72 ≤ 2503 ∧
    Row (primes 72) (states 72) (states 73) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
