import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_320 : 3 ≤ primes 320 ∧ primes 320 ≤ 2503 ∧
    Row (primes 320) (states 320) (states 321) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
