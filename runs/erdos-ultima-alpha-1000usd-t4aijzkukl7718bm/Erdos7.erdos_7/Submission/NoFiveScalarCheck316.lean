import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_316 : 3 ≤ primes 316 ∧ primes 316 ≤ 2503 ∧
    Row (primes 316) (states 316) (states 317) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
