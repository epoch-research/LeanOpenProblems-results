import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_260 : 3 ≤ primes 260 ∧ primes 260 ≤ 2503 ∧
    Row (primes 260) (states 260) (states 261) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
