import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_348 : 3 ≤ primes 348 ∧ primes 348 ≤ 2503 ∧
    Row (primes 348) (states 348) (states 349) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
