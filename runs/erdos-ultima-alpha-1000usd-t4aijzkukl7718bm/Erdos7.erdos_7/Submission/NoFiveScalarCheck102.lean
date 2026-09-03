import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_102 : 3 ≤ primes 102 ∧ primes 102 ≤ 2503 ∧
    Row (primes 102) (states 102) (states 103) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
