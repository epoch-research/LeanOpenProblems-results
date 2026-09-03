import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_182 : 3 ≤ primes 182 ∧ primes 182 ≤ 2503 ∧
    Row (primes 182) (states 182) (states 183) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
