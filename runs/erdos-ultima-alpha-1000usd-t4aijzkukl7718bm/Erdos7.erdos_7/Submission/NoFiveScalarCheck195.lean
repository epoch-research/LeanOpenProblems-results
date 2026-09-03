import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_195 : 3 ≤ primes 195 ∧ primes 195 ≤ 2503 ∧
    Row (primes 195) (states 195) (states 196) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
