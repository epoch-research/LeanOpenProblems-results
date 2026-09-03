import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_225 : 3 ≤ primes 225 ∧ primes 225 ≤ 2503 ∧
    Row (primes 225) (states 225) (states 226) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
