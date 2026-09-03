import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_184 : 3 ≤ primes 184 ∧ primes 184 ≤ 2503 ∧
    Row (primes 184) (states 184) (states 185) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
