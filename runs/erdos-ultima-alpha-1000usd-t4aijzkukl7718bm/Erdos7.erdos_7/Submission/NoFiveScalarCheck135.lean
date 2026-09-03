import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_135 : 3 ≤ primes 135 ∧ primes 135 ≤ 2503 ∧
    Row (primes 135) (states 135) (states 136) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
