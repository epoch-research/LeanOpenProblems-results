import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_98 : 3 ≤ primes 98 ∧ primes 98 ≤ 2503 ∧
    Row (primes 98) (states 98) (states 99) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
