import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_279 : 3 ≤ primes 279 ∧ primes 279 ≤ 2503 ∧
    Row (primes 279) (states 279) (states 280) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
