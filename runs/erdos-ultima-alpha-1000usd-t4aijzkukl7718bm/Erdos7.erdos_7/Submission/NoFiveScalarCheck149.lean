import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_149 : 3 ≤ primes 149 ∧ primes 149 ≤ 2503 ∧
    Row (primes 149) (states 149) (states 150) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
