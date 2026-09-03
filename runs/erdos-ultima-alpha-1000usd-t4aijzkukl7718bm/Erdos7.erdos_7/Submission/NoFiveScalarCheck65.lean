import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_65 : 3 ≤ primes 65 ∧ primes 65 ≤ 2503 ∧
    Row (primes 65) (states 65) (states 66) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
