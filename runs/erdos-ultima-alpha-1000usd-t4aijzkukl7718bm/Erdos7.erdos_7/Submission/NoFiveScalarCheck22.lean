import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_22 : 3 ≤ primes 22 ∧ primes 22 ≤ 2503 ∧
    Row (primes 22) (states 22) (states 23) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
