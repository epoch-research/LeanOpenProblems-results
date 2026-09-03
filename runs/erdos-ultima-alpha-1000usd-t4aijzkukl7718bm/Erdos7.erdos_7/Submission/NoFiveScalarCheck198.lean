import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_198 : 3 ≤ primes 198 ∧ primes 198 ≤ 2503 ∧
    Row (primes 198) (states 198) (states 199) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
