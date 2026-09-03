import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_39 : 3 ≤ primes 39 ∧ primes 39 ≤ 2503 ∧
    Row (primes 39) (states 39) (states 40) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
