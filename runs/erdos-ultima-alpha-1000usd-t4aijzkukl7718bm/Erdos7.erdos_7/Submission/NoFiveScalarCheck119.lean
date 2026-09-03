import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_119 : 3 ≤ primes 119 ∧ primes 119 ≤ 2503 ∧
    Row (primes 119) (states 119) (states 120) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
