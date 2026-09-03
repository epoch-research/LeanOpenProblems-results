import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_340 : 3 ≤ primes 340 ∧ primes 340 ≤ 2503 ∧
    Row (primes 340) (states 340) (states 341) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
