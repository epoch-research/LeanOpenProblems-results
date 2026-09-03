import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_207 : 3 ≤ primes 207 ∧ primes 207 ≤ 2503 ∧
    Row (primes 207) (states 207) (states 208) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
