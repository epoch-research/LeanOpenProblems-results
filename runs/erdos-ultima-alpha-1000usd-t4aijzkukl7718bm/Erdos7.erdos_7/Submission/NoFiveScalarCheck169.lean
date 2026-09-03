import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_169 : 3 ≤ primes 169 ∧ primes 169 ≤ 2503 ∧
    Row (primes 169) (states 169) (states 170) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
