import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_114 : 3 ≤ primes 114 ∧ primes 114 ≤ 2503 ∧
    Row (primes 114) (states 114) (states 115) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
