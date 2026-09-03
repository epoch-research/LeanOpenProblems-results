import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_247 : 3 ≤ primes 247 ∧ primes 247 ≤ 2503 ∧
    Row (primes 247) (states 247) (states 248) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
