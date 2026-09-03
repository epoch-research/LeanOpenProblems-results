import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_142 : 3 ≤ primes 142 ∧ primes 142 ≤ 2503 ∧
    Row (primes 142) (states 142) (states 143) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
