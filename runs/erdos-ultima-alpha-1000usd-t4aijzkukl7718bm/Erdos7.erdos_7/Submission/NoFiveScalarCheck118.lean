import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_118 : 3 ≤ primes 118 ∧ primes 118 ≤ 2503 ∧
    Row (primes 118) (states 118) (states 119) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
