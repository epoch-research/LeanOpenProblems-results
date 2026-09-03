import Submission.FullSieve29Result
import Submission.FiniteSievePerturbation

/-! The cutoff-29 candidate graph has an infinite component but also
arbitrarily large isolated Gaussian-prime vertices. This illustrates why an
unspecified infinite component does not give infinitude at a specified seed. -/
namespace Erdos952Investigation.FullSieve29Isolated
open FiniteSieveReduction ExceptionSieveReduction FiniteSievePerturbation
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma offset_certificate : ∀ a b : Fin 5,
    (a.val ≠ 2 ∨ b.val ≠ 2) → ((a : ℤ)-2)^2+((b : ℤ)-2)^2 < 9 →
    ∃ p : Fin 30, p.val.Prime ∧ p.val ∣ 384540 ∧
      ((372391+(a : ℤ)-2)^2+((b : ℤ)-2)^2)%(p.val : ℤ) = 0 := by
  decide +kernel


#print axioms offset_certificate
end Erdos952Investigation.FullSieve29Isolated
