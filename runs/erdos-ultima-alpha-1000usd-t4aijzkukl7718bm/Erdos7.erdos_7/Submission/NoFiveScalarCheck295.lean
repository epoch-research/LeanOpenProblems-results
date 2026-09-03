import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_295 : 3 ≤ primes 295 ∧ primes 295 ≤ 2503 ∧
    Row (primes 295) (states 295) (states 296) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
