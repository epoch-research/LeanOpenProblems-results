import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_319 : 3 ≤ primes 319 ∧ primes 319 ≤ 2503 ∧
    Row (primes 319) (states 319) (states 320) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
