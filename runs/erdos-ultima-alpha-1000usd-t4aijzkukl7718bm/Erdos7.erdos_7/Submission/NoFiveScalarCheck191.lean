import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_191 : 3 ≤ primes 191 ∧ primes 191 ≤ 2503 ∧
    Row (primes 191) (states 191) (states 192) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
