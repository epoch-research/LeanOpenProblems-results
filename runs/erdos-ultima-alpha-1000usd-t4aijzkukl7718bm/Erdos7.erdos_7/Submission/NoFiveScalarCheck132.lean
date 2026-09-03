import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_132 : 3 ≤ primes 132 ∧ primes 132 ≤ 2503 ∧
    Row (primes 132) (states 132) (states 133) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
