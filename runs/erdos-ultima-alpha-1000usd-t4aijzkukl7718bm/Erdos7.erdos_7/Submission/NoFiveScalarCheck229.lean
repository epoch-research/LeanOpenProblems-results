import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_229 : 3 ≤ primes 229 ∧ primes 229 ≤ 2503 ∧
    Row (primes 229) (states 229) (states 230) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
