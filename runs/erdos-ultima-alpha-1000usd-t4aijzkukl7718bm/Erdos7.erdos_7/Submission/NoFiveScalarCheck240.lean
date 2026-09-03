import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_240 : 3 ≤ primes 240 ∧ primes 240 ≤ 2503 ∧
    Row (primes 240) (states 240) (states 241) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
