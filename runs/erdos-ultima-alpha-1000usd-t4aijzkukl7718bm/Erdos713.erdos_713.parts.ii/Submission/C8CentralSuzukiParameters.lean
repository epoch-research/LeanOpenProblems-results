import FormalConjecturesUtil
import Submission.C8CentralSuzukiBasic
import Submission.C8SuzukiScalarExclusions

/-! Nonvanishing of every parameter in the rational central octagon. -/
namespace Erdos713C8CentralSuzukiParameters
open Erdos713C8CentralSuzukiMatrices Erdos713C8SuzukiScalarExclusions
variable {F : Type*} [Field F] [CharP F 2]

lemma nonzero (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc8 : c^8 ≠ c) :
    c ≠ 0 ∧ J σ c ≠ 0 ∧ A σ c ≠ 0 ∧ d σ c ≠ 0 ∧ e σ c ≠ 0 ∧
      f σ c ≠ 0 ∧ g σ c ≠ 0 ∧ h σ c ≠ 0 := by
  have hc := c_ne_zero hc8
  have hc1 := c_ne_one hc8
  have hC : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hJ : J σ c ≠ 0 := J_ne_zero σ hσ c hc8
  have hA : A σ c ≠ 0 := A_ne_zero σ hσ c hc8
  have hJJ : σ (J σ c) ≠ 0 := (map_ne_zero σ).mpr hJ
  have hAA : σ (A σ c) ≠ 0 := (map_ne_zero σ).mpr hA
  have hN := mul_ne_zero (first_sum_ne_zero σ hσ c hc hc1)
    (second_sum_ne_zero σ hσ c hc hc1)
  refine ⟨hc,hJ,hA,?_,?_,?_,?_,?_⟩
  · exact div_ne_zero hN (mul_ne_zero hJ hJJ)
  · exact div_ne_zero hN (mul_ne_zero hc hC)
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero 3 hc) hC) (mul_ne_zero hA hAA)
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hA) hAA)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hC) hJ) hJJ)
  · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ) hJJ) (mul_ne_zero hA hAA)

end Erdos713C8CentralSuzukiParameters
