import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_311 : 3 ≤ primes 311 ∧ primes 311 ≤ 2503 ∧
    Row (primes 311) (states 311) (states 312) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
