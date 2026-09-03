import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_170 : 3 ≤ primes 170 ∧ primes 170 ≤ 2503 ∧
    Row (primes 170) (states 170) (states 171) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
