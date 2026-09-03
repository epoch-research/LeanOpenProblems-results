import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_154 : 3 ≤ primes 154 ∧ primes 154 ≤ 2503 ∧
    Row (primes 154) (states 154) (states 155) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
