import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_252 : 3 ≤ primes 252 ∧ primes 252 ≤ 2503 ∧
    Row (primes 252) (states 252) (states 253) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
