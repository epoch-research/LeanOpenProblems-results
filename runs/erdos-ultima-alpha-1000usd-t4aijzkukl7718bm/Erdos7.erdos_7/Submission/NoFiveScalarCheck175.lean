import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_175 : 3 ≤ primes 175 ∧ primes 175 ≤ 2503 ∧
    Row (primes 175) (states 175) (states 176) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
