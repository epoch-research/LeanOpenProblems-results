import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_313 : 3 ≤ primes 313 ∧ primes 313 ≤ 2503 ∧
    Row (primes 313) (states 313) (states 314) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
