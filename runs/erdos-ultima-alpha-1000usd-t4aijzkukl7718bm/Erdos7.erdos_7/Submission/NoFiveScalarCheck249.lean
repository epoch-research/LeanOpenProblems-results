import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_249 : 3 ≤ primes 249 ∧ primes 249 ≤ 2503 ∧
    Row (primes 249) (states 249) (states 250) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
