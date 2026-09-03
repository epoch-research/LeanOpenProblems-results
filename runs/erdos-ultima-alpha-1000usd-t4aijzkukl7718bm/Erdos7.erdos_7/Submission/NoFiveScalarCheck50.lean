import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_50 : 3 ≤ primes 50 ∧ primes 50 ≤ 2503 ∧
    Row (primes 50) (states 50) (states 51) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
