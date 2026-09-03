import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_38 : 3 ≤ primes 38 ∧ primes 38 ≤ 2503 ∧
    Row (primes 38) (states 38) (states 39) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
