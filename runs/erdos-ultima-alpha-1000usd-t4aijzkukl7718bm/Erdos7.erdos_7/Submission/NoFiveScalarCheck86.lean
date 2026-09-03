import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_86 : 3 ≤ primes 86 ∧ primes 86 ≤ 2503 ∧
    Row (primes 86) (states 86) (states 87) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
