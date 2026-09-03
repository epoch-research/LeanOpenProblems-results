import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_328 : 3 ≤ primes 328 ∧ primes 328 ≤ 2503 ∧
    Row (primes 328) (states 328) (states 329) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
