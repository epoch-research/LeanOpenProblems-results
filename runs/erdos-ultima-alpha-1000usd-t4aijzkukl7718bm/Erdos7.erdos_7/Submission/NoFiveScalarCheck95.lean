import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_95 : 3 ≤ primes 95 ∧ primes 95 ≤ 2503 ∧
    Row (primes 95) (states 95) (states 96) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
