import Submission.NoFiveArithmetic
import Submission.NoFiveScalarCertificate

/-! Every distinct odd cover must use a modulus divisible by five.
This necessary condition does not settle the unrestricted odd-covering problem. -/
namespace Erdos7NoFive
open Erdos7Reduction

theorem arithmetic_exists_five {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) : ∃ i,5 ∣ m i :=
  Erdos7NoFiveArithmetic.arithmetic_exists_five Erdos7NoFiveScalar.certificate m a hc

theorem strict_exists_five (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) : ∃ i,5 ∣ (C.moduli i).absNorm :=
  Erdos7NoFiveArithmetic.strict_exists_five Erdos7NoFiveScalar.certificate C hodd

#print axioms arithmetic_exists_five
#print axioms strict_exists_five
end Erdos7NoFive
