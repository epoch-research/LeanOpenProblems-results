import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_145 : 3 ≤ primes 145 ∧ primes 145 ≤ 2503 ∧
    Row (primes 145) (states 145) (states 146) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
