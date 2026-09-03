import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_62 : 3 ≤ primes 62 ∧ primes 62 ≤ 2503 ∧
    Row (primes 62) (states 62) (states 63) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
