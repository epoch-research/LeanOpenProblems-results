import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_174 : 3 ≤ primes 174 ∧ primes 174 ≤ 2503 ∧
    Row (primes 174) (states 174) (states 175) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
