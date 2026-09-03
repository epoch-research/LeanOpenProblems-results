import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_20 : 3 ≤ primes 20 ∧ primes 20 ≤ 2503 ∧
    Row (primes 20) (states 20) (states 21) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
