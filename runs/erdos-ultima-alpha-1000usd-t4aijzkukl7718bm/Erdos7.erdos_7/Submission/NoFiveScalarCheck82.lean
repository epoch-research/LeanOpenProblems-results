import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_82 : 3 ≤ primes 82 ∧ primes 82 ≤ 2503 ∧
    Row (primes 82) (states 82) (states 83) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
