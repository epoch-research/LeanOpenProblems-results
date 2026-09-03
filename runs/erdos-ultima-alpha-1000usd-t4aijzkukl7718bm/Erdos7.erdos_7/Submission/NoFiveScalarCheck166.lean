import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_166 : 3 ≤ primes 166 ∧ primes 166 ≤ 2503 ∧
    Row (primes 166) (states 166) (states 167) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
