import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_2 : 3 ≤ primes 2 ∧ primes 2 ≤ 2503 ∧
    Row (primes 2) (states 2) (states 3) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
