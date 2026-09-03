import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_63 : 3 ≤ primes 63 ∧ primes 63 ≤ 2503 ∧
    Row (primes 63) (states 63) (states 64) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
