import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_193 : 3 ≤ primes 193 ∧ primes 193 ≤ 2503 ∧
    Row (primes 193) (states 193) (states 194) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
