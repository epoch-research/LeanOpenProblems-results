import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_133 : 3 ≤ primes 133 ∧ primes 133 ≤ 2503 ∧
    Row (primes 133) (states 133) (states 134) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
