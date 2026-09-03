import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_213 : 3 ≤ primes 213 ∧ primes 213 ≤ 2503 ∧
    Row (primes 213) (states 213) (states 214) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
