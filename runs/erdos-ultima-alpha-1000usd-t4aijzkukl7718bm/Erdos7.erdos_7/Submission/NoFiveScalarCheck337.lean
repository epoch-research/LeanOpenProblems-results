import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_337 : 3 ≤ primes 337 ∧ primes 337 ≤ 2503 ∧
    Row (primes 337) (states 337) (states 338) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
