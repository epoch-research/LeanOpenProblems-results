import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_34 : 3 ≤ primes 34 ∧ primes 34 ≤ 2503 ∧
    Row (primes 34) (states 34) (states 35) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
