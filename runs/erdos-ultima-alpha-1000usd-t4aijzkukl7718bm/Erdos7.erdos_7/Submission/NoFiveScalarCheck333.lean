import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_333 : 3 ≤ primes 333 ∧ primes 333 ≤ 2503 ∧
    Row (primes 333) (states 333) (states 334) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
