import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_81 : 3 ≤ primes 81 ∧ primes 81 ≤ 2503 ∧
    Row (primes 81) (states 81) (states 82) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
