import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_23 : 3 ≤ primes 23 ∧ primes 23 ≤ 2503 ∧
    Row (primes 23) (states 23) (states 24) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
