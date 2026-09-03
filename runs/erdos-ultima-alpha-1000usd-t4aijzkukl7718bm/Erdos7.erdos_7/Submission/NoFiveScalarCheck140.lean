import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_140 : 3 ≤ primes 140 ∧ primes 140 ≤ 2503 ∧
    Row (primes 140) (states 140) (states 141) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
