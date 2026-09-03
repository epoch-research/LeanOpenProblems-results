import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_129 : 3 ≤ primes 129 ∧ primes 129 ≤ 2503 ∧
    Row (primes 129) (states 129) (states 130) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
