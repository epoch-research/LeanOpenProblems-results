import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_150 : 3 ≤ primes 150 ∧ primes 150 ≤ 2503 ∧
    Row (primes 150) (states 150) (states 151) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
