import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_26 : 3 ≤ primes 26 ∧ primes 26 ≤ 2503 ∧
    Row (primes 26) (states 26) (states 27) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
