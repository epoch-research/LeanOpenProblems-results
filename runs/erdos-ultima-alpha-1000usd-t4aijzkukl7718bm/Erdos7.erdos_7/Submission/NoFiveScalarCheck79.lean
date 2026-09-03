import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_79 : 3 ≤ primes 79 ∧ primes 79 ≤ 2503 ∧
    Row (primes 79) (states 79) (states 80) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
