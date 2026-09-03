import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_68 : 3 ≤ primes 68 ∧ primes 68 ≤ 2503 ∧
    Row (primes 68) (states 68) (states 69) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
