import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_181 : 3 ≤ primes 181 ∧ primes 181 ≤ 2503 ∧
    Row (primes 181) (states 181) (states 182) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
