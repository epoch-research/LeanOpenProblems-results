import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_30 : 3 ≤ primes 30 ∧ primes 30 ≤ 2503 ∧
    Row (primes 30) (states 30) (states 31) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
