import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_14 : 3 ≤ primes 14 ∧ primes 14 ≤ 2503 ∧
    Row (primes 14) (states 14) (states 15) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
