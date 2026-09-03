import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_171 : 3 ≤ primes 171 ∧ primes 171 ≤ 2503 ∧
    Row (primes 171) (states 171) (states 172) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
