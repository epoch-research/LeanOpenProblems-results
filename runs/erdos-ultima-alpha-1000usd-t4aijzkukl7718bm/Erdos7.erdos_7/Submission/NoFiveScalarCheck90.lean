import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_90 : 3 ≤ primes 90 ∧ primes 90 ≤ 2503 ∧
    Row (primes 90) (states 90) (states 91) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
