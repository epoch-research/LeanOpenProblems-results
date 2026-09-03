import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_324 : 3 ≤ primes 324 ∧ primes 324 ≤ 2503 ∧
    Row (primes 324) (states 324) (states 325) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
