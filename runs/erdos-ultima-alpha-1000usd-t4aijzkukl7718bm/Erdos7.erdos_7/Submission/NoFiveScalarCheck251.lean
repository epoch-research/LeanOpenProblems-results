import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_251 : 3 ≤ primes 251 ∧ primes 251 ≤ 2503 ∧
    Row (primes 251) (states 251) (states 252) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
