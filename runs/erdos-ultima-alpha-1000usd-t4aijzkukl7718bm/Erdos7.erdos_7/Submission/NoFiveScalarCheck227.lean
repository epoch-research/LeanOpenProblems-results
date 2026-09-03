import Submission.NoFiveScalarData
namespace Erdos7NoFiveScalar
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000
lemma row_certificate_227 : 3 ≤ primes 227 ∧ primes 227 ≤ 2503 ∧
    Row (primes 227) (states 227) (states 228) := by
  unfold Row State.Good
  decide +kernel
end Erdos7NoFiveScalar
