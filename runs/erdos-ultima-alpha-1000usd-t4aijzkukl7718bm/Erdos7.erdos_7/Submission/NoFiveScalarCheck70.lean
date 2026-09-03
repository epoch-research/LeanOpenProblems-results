import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_70 : 3 ≤ primes 70 ∧ primes 70 ≤ 2503 ∧
    Row (primes 70) (states 70) (states 71) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
