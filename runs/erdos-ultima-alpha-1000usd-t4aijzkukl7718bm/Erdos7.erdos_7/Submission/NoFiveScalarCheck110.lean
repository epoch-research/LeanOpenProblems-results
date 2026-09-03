import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_110 : 3 ≤ primes 110 ∧ primes 110 ≤ 2503 ∧
    Row (primes 110) (states 110) (states 111) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
