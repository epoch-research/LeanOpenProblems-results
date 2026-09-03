import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_67 : 3 ≤ primes 67 ∧ primes 67 ≤ 2503 ∧
    Row (primes 67) (states 67) (states 68) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
