import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_167 : 3 ≤ primes 167 ∧ primes 167 ≤ 2503 ∧
    Row (primes 167) (states 167) (states 168) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
