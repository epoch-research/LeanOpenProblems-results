import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_88 : 3 ≤ primes 88 ∧ primes 88 ≤ 2503 ∧
    Row (primes 88) (states 88) (states 89) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
