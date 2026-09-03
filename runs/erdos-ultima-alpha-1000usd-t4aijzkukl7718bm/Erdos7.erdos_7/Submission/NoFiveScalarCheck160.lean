import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_160 : 3 ≤ primes 160 ∧ primes 160 ≤ 2503 ∧
    Row (primes 160) (states 160) (states 161) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
