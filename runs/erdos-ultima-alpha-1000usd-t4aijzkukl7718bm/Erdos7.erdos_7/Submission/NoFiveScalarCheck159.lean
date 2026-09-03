import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_159 : 3 ≤ primes 159 ∧ primes 159 ≤ 2503 ∧
    Row (primes 159) (states 159) (states 160) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
