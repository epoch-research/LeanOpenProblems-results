import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_187 : 3 ≤ primes 187 ∧ primes 187 ≤ 2503 ∧
    Row (primes 187) (states 187) (states 188) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
