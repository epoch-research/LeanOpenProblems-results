import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_262 : 3 ≤ primes 262 ∧ primes 262 ≤ 2503 ∧
    Row (primes 262) (states 262) (states 263) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
