import FormalConjecturesUtil
import Submission.C8CentralSuzukiBasic

/-! A rational octagon identity for opposite twisted central matrices. -/
namespace Erdos713C8CentralSuzukiMatrices
open Erdos713C8MixedSuzukiMatrices
variable {F : Type*} [Field F] [CharP F 2]
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

lemma word_row0 (σ : F →+* F) (hσ : ∀ x, σ (σ x)=x^2)
    (c : F) (hc : c ≠ 0) (hJ : J σ c ≠ 0) (hA : A σ c ≠ 0) :
    ∀ j : Fin 4, (Z σ 1*O σ 1*Z σ c*O σ (d σ c)*Z σ (h σ c)) 0 j =
      (O σ (e σ c)*Z σ (f σ c)*O σ (g σ c)) 0 j := by
  have hC : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  have hJJ : σ (J σ c) ≠ 0 := (map_ne_zero σ).mpr hJ
  have hAA : σ (A σ c) ≠ 0 := (map_ne_zero σ).mpr hA
  have hJ2 := pow_ne_zero 2 hJ
  have hA2 := pow_ne_zero 2 hA
  simp only [J,A,map_add,map_mul,map_pow,hσ] at hJ hA hJJ hAA hJ2 hA2
  ring_nf at hJ hA hJJ hAA hJ2 hA2
  reduce_mod_char! at hJ hA hJJ hAA hJ2 hA2
  have h0 : c*(c+1)+σ c ≠ 0 := by convert hJ using 1; ring
  have h1 : σ c*(σ c+1)+c^2 ≠ 0 := by convert hJJ using 1; ring
  have h2 : c*(c+σ c)+σ c ≠ 0 := by convert hA using 1; ring
  have h3 : σ c*(σ c+c^2)+c^2 ≠ 0 := by convert hAA using 1; ring
  have h4 : c^2*(c^2+1)+(σ c)^2 ≠ 0 := by convert hJ2 using 1; ring
  have h5 : c^2*(c^2+(σ c)^2)+(σ c)^2 ≠ 0 := by convert hA2 using 1; ring
  intro j
  fin_cases j
  all_goals
    (simp [Z,O,X,Matrix.mul_apply,Fin.sum_univ_succ];
      ring_nf; reduce_mod_char!;
      simp only [d,e,f,g,h,J,A,map_div₀,map_mul,map_add,map_pow,hσ];
      field_simp [hc,hC,h0,h1,h2,h3,h4,h5];
      ring_nf; reduce_mod_char!)

end Erdos713C8CentralSuzukiMatrices
