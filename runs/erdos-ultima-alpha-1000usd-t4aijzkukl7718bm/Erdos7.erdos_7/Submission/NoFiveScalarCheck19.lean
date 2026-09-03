import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_19 : 3 ≤ primes 19 ∧ primes 19 ≤ 2503 ∧
    Row (primes 19) (states 19) (states 20) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
