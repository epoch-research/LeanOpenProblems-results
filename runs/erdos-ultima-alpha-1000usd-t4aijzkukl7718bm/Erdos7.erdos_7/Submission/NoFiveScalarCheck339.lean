import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_339 : 3 ≤ primes 339 ∧ primes 339 ≤ 2503 ∧
    Row (primes 339) (states 339) (states 340) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
