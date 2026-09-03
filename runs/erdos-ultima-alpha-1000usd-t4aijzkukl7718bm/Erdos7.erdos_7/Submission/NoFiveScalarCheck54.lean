import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_54 : 3 ≤ primes 54 ∧ primes 54 ≤ 2503 ∧
    Row (primes 54) (states 54) (states 55) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
