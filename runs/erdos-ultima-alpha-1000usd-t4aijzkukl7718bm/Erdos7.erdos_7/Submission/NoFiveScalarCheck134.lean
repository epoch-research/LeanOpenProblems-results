import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_134 : 3 ≤ primes 134 ∧ primes 134 ≤ 2503 ∧
    Row (primes 134) (states 134) (states 135) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
