import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_25 : 3 ≤ primes 25 ∧ primes 25 ≤ 2503 ∧
    Row (primes 25) (states 25) (states 26) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
