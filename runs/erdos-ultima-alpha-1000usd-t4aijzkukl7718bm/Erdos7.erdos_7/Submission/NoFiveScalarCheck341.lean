import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_341 : 3 ≤ primes 341 ∧ primes 341 ≤ 2503 ∧
    Row (primes 341) (states 341) (states 342) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
