import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_44 : 3 ≤ primes 44 ∧ primes 44 ≤ 2503 ∧
    Row (primes 44) (states 44) (states 45) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
