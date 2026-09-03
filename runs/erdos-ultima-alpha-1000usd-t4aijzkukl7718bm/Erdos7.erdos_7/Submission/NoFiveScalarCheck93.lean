import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_93 : 3 ≤ primes 93 ∧ primes 93 ≤ 2503 ∧
    Row (primes 93) (states 93) (states 94) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
