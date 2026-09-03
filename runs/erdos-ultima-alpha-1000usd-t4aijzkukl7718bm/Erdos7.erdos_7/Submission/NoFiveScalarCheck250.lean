import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_250 : 3 ≤ primes 250 ∧ primes 250 ≤ 2503 ∧
    Row (primes 250) (states 250) (states 251) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
