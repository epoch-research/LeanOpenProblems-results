import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_107 : 3 ≤ primes 107 ∧ primes 107 ≤ 2503 ∧
    Row (primes 107) (states 107) (states 108) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
