import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_183 : 3 ≤ primes 183 ∧ primes 183 ≤ 2503 ∧
    Row (primes 183) (states 183) (states 184) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
