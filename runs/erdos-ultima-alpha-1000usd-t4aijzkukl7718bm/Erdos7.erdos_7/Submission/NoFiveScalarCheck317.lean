import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_317 : 3 ≤ primes 317 ∧ primes 317 ≤ 2503 ∧
    Row (primes 317) (states 317) (states 318) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
