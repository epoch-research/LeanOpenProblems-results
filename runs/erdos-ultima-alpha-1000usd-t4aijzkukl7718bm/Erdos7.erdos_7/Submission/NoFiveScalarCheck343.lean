import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_343 : 3 ≤ primes 343 ∧ primes 343 ≤ 2503 ∧
    Row (primes 343) (states 343) (states 344) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
