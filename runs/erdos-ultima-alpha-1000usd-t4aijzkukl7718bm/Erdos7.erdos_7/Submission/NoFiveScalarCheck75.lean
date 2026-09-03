import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_75 : 3 ≤ primes 75 ∧ primes 75 ≤ 2503 ∧
    Row (primes 75) (states 75) (states 76) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
