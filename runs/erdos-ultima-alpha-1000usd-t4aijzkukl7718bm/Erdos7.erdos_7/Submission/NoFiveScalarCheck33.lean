import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_33 : 3 ≤ primes 33 ∧ primes 33 ≤ 2503 ∧
    Row (primes 33) (states 33) (states 34) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
