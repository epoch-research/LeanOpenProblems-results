import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_335 : 3 ≤ primes 335 ∧ primes 335 ≤ 2503 ∧
    Row (primes 335) (states 335) (states 336) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
