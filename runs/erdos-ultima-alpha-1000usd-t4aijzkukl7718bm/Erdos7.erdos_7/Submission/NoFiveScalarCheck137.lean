import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_137 : 3 ≤ primes 137 ∧ primes 137 ≤ 2503 ∧
    Row (primes 137) (states 137) (states 138) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
