import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_120 : 3 ≤ primes 120 ∧ primes 120 ≤ 2503 ∧
    Row (primes 120) (states 120) (states 121) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
