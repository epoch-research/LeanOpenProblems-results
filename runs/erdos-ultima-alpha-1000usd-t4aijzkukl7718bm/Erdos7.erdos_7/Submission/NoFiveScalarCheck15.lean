import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_15 : 3 ≤ primes 15 ∧ primes 15 ≤ 2503 ∧
    Row (primes 15) (states 15) (states 16) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
