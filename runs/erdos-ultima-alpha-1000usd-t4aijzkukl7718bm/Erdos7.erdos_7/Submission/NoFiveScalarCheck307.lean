import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_307 : 3 ≤ primes 307 ∧ primes 307 ≤ 2503 ∧
    Row (primes 307) (states 307) (states 308) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
