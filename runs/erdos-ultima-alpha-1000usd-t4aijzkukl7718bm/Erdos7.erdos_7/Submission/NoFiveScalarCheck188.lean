import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_188 : 3 ≤ primes 188 ∧ primes 188 ≤ 2503 ∧
    Row (primes 188) (states 188) (states 189) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
