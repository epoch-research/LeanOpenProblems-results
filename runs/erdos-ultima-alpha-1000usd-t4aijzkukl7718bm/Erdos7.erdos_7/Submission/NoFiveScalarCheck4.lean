import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_4 : 3 ≤ primes 4 ∧ primes 4 ≤ 2503 ∧
    Row (primes 4) (states 4) (states 5) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
