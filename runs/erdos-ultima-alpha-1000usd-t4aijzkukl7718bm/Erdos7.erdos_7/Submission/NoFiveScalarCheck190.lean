import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_190 : 3 ≤ primes 190 ∧ primes 190 ≤ 2503 ∧
    Row (primes 190) (states 190) (states 191) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
