import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_281 : 3 ≤ primes 281 ∧ primes 281 ≤ 2503 ∧
    Row (primes 281) (states 281) (states 282) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
