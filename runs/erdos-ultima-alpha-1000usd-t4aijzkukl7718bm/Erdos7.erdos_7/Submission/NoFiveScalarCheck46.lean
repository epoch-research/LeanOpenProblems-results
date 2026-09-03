import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_46 : 3 ≤ primes 46 ∧ primes 46 ≤ 2503 ∧
    Row (primes 46) (states 46) (states 47) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
