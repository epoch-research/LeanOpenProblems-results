import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_302 : 3 ≤ primes 302 ∧ primes 302 ≤ 2503 ∧
    Row (primes 302) (states 302) (states 303) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
