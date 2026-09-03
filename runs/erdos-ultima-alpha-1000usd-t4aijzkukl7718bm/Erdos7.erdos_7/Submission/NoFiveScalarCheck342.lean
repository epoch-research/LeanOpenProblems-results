import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_342 : 3 ≤ primes 342 ∧ primes 342 ≤ 2503 ∧
    Row (primes 342) (states 342) (states 343) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
