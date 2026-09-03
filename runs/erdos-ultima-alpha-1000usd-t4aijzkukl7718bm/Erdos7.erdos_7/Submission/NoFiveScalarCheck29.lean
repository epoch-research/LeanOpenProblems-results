import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_29 : 3 ≤ primes 29 ∧ primes 29 ≤ 2503 ∧
    Row (primes 29) (states 29) (states 30) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
