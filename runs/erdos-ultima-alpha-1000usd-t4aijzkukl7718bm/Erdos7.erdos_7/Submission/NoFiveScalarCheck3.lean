import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_3 : 3 ≤ primes 3 ∧ primes 3 ≤ 2503 ∧
    Row (primes 3) (states 3) (states 4) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
