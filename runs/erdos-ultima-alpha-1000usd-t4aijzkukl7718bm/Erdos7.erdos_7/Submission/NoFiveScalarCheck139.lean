import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_139 : 3 ≤ primes 139 ∧ primes 139 ≤ 2503 ∧
    Row (primes 139) (states 139) (states 140) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
