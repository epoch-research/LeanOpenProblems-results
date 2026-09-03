import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_125 : 3 ≤ primes 125 ∧ primes 125 ≤ 2503 ∧
    Row (primes 125) (states 125) (states 126) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
