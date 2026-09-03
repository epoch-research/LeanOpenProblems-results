import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_310 : 3 ≤ primes 310 ∧ primes 310 ≤ 2503 ∧
    Row (primes 310) (states 310) (states 311) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
