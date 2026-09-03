import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_45 : 3 ≤ primes 45 ∧ primes 45 ≤ 2503 ∧
    Row (primes 45) (states 45) (states 46) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
