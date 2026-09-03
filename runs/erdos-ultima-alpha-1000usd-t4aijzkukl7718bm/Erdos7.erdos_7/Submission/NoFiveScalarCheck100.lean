import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_100 : 3 ≤ primes 100 ∧ primes 100 ≤ 2503 ∧
    Row (primes 100) (states 100) (states 101) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
