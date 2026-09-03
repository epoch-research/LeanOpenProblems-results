import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_47 : 3 ≤ primes 47 ∧ primes 47 ≤ 2503 ∧
    Row (primes 47) (states 47) (states 48) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
