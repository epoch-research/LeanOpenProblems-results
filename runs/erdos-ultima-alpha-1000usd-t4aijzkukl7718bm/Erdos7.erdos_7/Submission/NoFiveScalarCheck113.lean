import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_113 : 3 ≤ primes 113 ∧ primes 113 ≤ 2503 ∧
    Row (primes 113) (states 113) (states 114) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
