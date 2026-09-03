import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_71 : 3 ≤ primes 71 ∧ primes 71 ≤ 2503 ∧
    Row (primes 71) (states 71) (states 72) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
