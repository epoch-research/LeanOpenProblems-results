import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_109 : 3 ≤ primes 109 ∧ primes 109 ≤ 2503 ∧
    Row (primes 109) (states 109) (states 110) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
