import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_101 : 3 ≤ primes 101 ∧ primes 101 ≤ 2503 ∧
    Row (primes 101) (states 101) (states 102) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
