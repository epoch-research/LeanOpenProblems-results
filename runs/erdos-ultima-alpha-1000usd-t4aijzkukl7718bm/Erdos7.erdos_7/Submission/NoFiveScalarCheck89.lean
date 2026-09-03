import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_89 : 3 ≤ primes 89 ∧ primes 89 ≤ 2503 ∧
    Row (primes 89) (states 89) (states 90) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
