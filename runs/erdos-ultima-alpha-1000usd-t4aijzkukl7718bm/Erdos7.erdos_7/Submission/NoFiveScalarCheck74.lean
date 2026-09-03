import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_74 : 3 ≤ primes 74 ∧ primes 74 ≤ 2503 ∧
    Row (primes 74) (states 74) (states 75) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
