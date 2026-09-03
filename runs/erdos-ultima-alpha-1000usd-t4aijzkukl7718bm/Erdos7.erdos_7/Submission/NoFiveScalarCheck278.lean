import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_278 : 3 ≤ primes 278 ∧ primes 278 ≤ 2503 ∧
    Row (primes 278) (states 278) (states 279) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
