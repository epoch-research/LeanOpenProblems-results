import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_41 : 3 ≤ primes 41 ∧ primes 41 ≤ 2503 ∧
    Row (primes 41) (states 41) (states 42) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
