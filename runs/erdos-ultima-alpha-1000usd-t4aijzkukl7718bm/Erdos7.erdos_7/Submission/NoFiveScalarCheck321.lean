import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_321 : 3 ≤ primes 321 ∧ primes 321 ≤ 2503 ∧
    Row (primes 321) (states 321) (states 322) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
