import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_94 : 3 ≤ primes 94 ∧ primes 94 ≤ 2503 ∧
    Row (primes 94) (states 94) (states 95) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
