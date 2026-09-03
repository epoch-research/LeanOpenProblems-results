import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_315 : 3 ≤ primes 315 ∧ primes 315 ≤ 2503 ∧
    Row (primes 315) (states 315) (states 316) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
