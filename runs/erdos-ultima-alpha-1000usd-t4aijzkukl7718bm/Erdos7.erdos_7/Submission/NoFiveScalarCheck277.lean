import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_277 : 3 ≤ primes 277 ∧ primes 277 ≤ 2503 ∧
    Row (primes 277) (states 277) (states 278) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
