import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_59 : 3 ≤ primes 59 ∧ primes 59 ≤ 2503 ∧
    Row (primes 59) (states 59) (states 60) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
