import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_66 : 3 ≤ primes 66 ∧ primes 66 ≤ 2503 ∧
    Row (primes 66) (states 66) (states 67) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
