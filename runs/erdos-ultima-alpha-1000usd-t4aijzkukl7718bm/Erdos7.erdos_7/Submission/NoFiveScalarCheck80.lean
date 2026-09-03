import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_80 : 3 ≤ primes 80 ∧ primes 80 ≤ 2503 ∧
    Row (primes 80) (states 80) (states 81) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
