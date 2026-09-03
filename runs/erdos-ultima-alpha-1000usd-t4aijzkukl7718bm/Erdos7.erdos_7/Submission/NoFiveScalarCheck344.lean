import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_344 : 3 ≤ primes 344 ∧ primes 344 ≤ 2503 ∧
    Row (primes 344) (states 344) (states 345) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
