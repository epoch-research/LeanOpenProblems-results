import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_138 : 3 ≤ primes 138 ∧ primes 138 ≤ 2503 ∧
    Row (primes 138) (states 138) (states 139) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
