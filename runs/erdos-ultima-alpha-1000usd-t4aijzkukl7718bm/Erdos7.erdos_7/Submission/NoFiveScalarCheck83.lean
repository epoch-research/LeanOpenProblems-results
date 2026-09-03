import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_83 : 3 ≤ primes 83 ∧ primes 83 ≤ 2503 ∧
    Row (primes 83) (states 83) (states 84) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
