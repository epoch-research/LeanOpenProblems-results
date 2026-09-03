import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_91 : 3 ≤ primes 91 ∧ primes 91 ≤ 2503 ∧
    Row (primes 91) (states 91) (states 92) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
