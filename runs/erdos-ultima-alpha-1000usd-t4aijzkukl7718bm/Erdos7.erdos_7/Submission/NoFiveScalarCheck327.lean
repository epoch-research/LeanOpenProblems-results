import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_327 : 3 ≤ primes 327 ∧ primes 327 ≤ 2503 ∧
    Row (primes 327) (states 327) (states 328) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
