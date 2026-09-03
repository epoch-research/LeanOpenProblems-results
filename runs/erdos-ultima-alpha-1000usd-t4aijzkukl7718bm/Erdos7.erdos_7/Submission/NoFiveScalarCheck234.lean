import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_234 : 3 ≤ primes 234 ∧ primes 234 ≤ 2503 ∧
    Row (primes 234) (states 234) (states 235) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
