import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_347 : 3 ≤ primes 347 ∧ primes 347 ≤ 2503 ∧
    Row (primes 347) (states 347) (states 348) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
