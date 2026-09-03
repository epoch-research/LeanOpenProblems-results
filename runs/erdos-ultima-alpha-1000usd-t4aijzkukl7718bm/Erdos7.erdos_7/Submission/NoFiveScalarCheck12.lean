import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_12 : 3 ≤ primes 12 ∧ primes 12 ≤ 2503 ∧
    Row (primes 12) (states 12) (states 13) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
