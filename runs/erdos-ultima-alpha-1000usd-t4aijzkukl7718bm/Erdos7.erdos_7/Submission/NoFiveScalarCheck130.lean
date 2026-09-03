import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_130 : 3 ≤ primes 130 ∧ primes 130 ≤ 2503 ∧
    Row (primes 130) (states 130) (states 131) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
