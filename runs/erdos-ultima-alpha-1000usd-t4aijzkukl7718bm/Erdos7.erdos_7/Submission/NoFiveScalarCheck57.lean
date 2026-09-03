import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_57 : 3 ≤ primes 57 ∧ primes 57 ≤ 2503 ∧
    Row (primes 57) (states 57) (states 58) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
