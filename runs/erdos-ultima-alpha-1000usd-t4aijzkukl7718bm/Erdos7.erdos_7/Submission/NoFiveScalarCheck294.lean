import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_294 : 3 ≤ primes 294 ∧ primes 294 ≤ 2503 ∧
    Row (primes 294) (states 294) (states 295) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
