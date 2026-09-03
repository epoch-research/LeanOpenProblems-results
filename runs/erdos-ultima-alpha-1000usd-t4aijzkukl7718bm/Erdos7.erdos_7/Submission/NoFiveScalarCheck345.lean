import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_345 : 3 ≤ primes 345 ∧ primes 345 ≤ 2503 ∧
    Row (primes 345) (states 345) (states 346) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
