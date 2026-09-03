import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_49 : 3 ≤ primes 49 ∧ primes 49 ≤ 2503 ∧
    Row (primes 49) (states 49) (states 50) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
