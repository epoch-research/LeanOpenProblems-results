import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_304 : 3 ≤ primes 304 ∧ primes 304 ≤ 2503 ∧
    Row (primes 304) (states 304) (states 305) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
