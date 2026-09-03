import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_248 : 3 ≤ primes 248 ∧ primes 248 ≤ 2503 ∧
    Row (primes 248) (states 248) (states 249) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
