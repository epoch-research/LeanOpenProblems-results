import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_211 : 3 ≤ primes 211 ∧ primes 211 ≤ 2503 ∧
    Row (primes 211) (states 211) (states 212) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
