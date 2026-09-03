import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_232 : 3 ≤ primes 232 ∧ primes 232 ≤ 2503 ∧
    Row (primes 232) (states 232) (states 233) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
