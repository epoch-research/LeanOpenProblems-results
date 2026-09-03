import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_131 : 3 ≤ primes 131 ∧ primes 131 ≤ 2503 ∧
    Row (primes 131) (states 131) (states 132) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
