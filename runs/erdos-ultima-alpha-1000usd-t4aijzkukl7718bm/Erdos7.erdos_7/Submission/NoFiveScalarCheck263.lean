import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_263 : 3 ≤ primes 263 ∧ primes 263 ≤ 2503 ∧
    Row (primes 263) (states 263) (states 264) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
