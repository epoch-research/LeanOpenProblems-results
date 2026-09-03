import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_322 : 3 ≤ primes 322 ∧ primes 322 ≤ 2503 ∧
    Row (primes 322) (states 322) (states 323) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
