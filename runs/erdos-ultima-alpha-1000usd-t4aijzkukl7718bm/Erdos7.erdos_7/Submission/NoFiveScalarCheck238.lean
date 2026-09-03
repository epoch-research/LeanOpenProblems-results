import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_238 : 3 ≤ primes 238 ∧ primes 238 ≤ 2503 ∧
    Row (primes 238) (states 238) (states 239) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
