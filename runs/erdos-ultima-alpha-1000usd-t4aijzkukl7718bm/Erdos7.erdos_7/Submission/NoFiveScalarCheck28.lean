import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_28 : 3 ≤ primes 28 ∧ primes 28 ≤ 2503 ∧
    Row (primes 28) (states 28) (states 29) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
