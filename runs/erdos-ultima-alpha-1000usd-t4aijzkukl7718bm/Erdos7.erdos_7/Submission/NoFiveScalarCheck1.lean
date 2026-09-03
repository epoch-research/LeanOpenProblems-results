import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_1 : 3 ≤ primes 1 ∧ primes 1 ≤ 2503 ∧
    Row (primes 1) (states 1) (states 2) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
