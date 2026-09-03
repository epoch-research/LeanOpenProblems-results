import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_275 : 3 ≤ primes 275 ∧ primes 275 ≤ 2503 ∧
    Row (primes 275) (states 275) (states 276) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
