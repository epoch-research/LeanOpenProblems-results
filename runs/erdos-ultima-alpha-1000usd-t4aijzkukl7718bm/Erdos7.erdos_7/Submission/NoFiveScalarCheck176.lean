import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_176 : 3 ≤ primes 176 ∧ primes 176 ≤ 2503 ∧
    Row (primes 176) (states 176) (states 177) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
