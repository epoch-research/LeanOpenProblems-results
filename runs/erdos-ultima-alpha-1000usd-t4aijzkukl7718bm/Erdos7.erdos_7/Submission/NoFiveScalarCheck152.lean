import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_152 : 3 ≤ primes 152 ∧ primes 152 ≤ 2503 ∧
    Row (primes 152) (states 152) (states 153) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
