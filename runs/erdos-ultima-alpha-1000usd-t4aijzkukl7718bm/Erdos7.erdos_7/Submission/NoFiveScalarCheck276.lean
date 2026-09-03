import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_276 : 3 ≤ primes 276 ∧ primes 276 ≤ 2503 ∧
    Row (primes 276) (states 276) (states 277) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
