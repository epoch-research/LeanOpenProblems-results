import Submission.LinearFormsUniformity

/-! Square-root cancellation for nonzero binary quadratic forms over finite
fields of odd characteristic. This supplies a concrete discrepancy input,
without asserting it for arbitrary higher-order factors. -/
namespace Erdos3BinaryQuadraticGauss
open Finset Erdos3FiniteFourier Erdos3QuadraticFourAPBarrier Erdos3LinearFormsUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 3000000

variable {F : Type*} [Field F] [Fintype F]

lemma primitive_characters_parameterized (χ : AddChar F ℂ) (hχ : χ.IsPrimitive) :
    Function.Surjective χ.mulShift :=
  ((Fintype.bijective_iff_injective_and_card χ.mulShift).mpr
    ⟨AddChar.to_mulShift_inj_of_isPrimitive hχ,by simp⟩).2

lemma quadratic_linear_mean_sq (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    ‖𝔼 x : F, χ (a*x^2+b*x+c)‖^2 = 1/(Fintype.card F : ℝ) := by
  have he : (𝔼 x : F, χ (a*x^2+b*x+c)) =
      χ c*hat (quadraticPhase χ a) (χ.mulShift (-b)) := by
    rw [hat,mul_expect]
    apply expect_congr rfl
    intro x _
    simp only [quadraticPhase,AddChar.mulShift_apply,← char_sub,← χ.map_add_eq_mul]
    congr 1
    ring
  rw [he,norm_mul,χ.norm_apply,one_mul]
  exact quadratic_hat_norm_sq χ hχ h2 ha _

noncomputable def binaryQuadraticMean (χ : AddChar F ℂ) (a b c : F) : ℂ :=
  𝔼 x : F, 𝔼 y : F, χ (a*x^2+b*x*y+c*y^2)

lemma binaryQuadraticMean_swap (χ : AddChar F ℂ) (a b c : F) :
    binaryQuadraticMean χ a b c = binaryQuadraticMean χ c b a := by
  unfold binaryQuadraticMean
  rw [expect_comm]
  apply expect_congr rfl
  intro y _
  apply expect_congr rfl
  intro x _
  congr 1
  ring

lemma binaryQuadraticMean_sq_le_of_first (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0) (b c : F) :
    ‖binaryQuadraticMean χ a b c‖^2 ≤ 1/(Fintype.card F : ℝ) := by
  unfold binaryQuadraticMean
  rw [expect_comm]
  have h := mean_product_sq_le (fun _y : F ↦ (1 : ℂ))
    (fun y ↦ 𝔼 x : F, χ (a*x^2+b*x*y+c*y^2)) (fun _ ↦ by norm_num)
  simp only [one_mul] at h
  apply h.trans_eq
  have hs (y : F) : ‖𝔼 x : F, χ (a*x^2+b*x*y+c*y^2)‖^2 = 1/(Fintype.card F : ℝ) := by
    convert quadratic_linear_mean_sq χ hχ h2 ha (b*y) (c*y^2) using 2
    congr 1
    apply expect_congr rfl
    intro x _
    congr 1
    ring
  simp only [hs,Fintype.expect_const]

/-- A shear makes a nonzero mixed term into a nonzero square coefficient. -/
lemma binaryQuadraticMean_shear (χ : AddChar F ℂ) (a b c : F) :
    binaryQuadraticMean χ a b c = binaryQuadraticMean χ (a+b+c) (b+2*c) c := by
  unfold binaryQuadraticMean
  apply expect_congr rfl
  intro x _
  symm
  apply Fintype.expect_equiv (Equiv.addRight x)
  intro y
  congr 1
  change (a+b+c)*x^2+(b+2*c)*x*y+c*y^2 = a*x^2+b*x*(y+x)+c*(y+x)^2
  ring

/-- Every nonzero binary quadratic form has normalized character average at
most the square root of the reciprocal field size. -/
theorem binaryQuadraticMean_sq_le (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) (a b c : F) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ‖binaryQuadraticMean χ a b c‖^2 ≤ 1/(Fintype.card F : ℝ) := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · have hb : b ≠ 0 := by tauto
      subst a
      subst c
      rw [binaryQuadraticMean_shear]
      simp only [zero_add,add_zero,mul_zero]
      exact binaryQuadraticMean_sq_le_of_first χ hχ h2 hb b 0
    · rw [binaryQuadraticMean_swap]
      exact binaryQuadraticMean_sq_le_of_first χ hχ h2 hc b a
  · exact binaryQuadraticMean_sq_le_of_first χ hχ h2 ha b c

theorem binaryQuadraticMean_norm_le (χ : AddChar F ℂ) (hχ : χ.IsPrimitive)
    (h2 : (2 : F) ≠ 0) (a b c : F) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ‖binaryQuadraticMean χ a b c‖ ≤ Real.sqrt (1/(Fintype.card F : ℝ)) :=
  Real.le_sqrt_of_sq_le (binaryQuadraticMean_sq_le χ hχ h2 a b c h)

#print axioms quadratic_linear_mean_sq
#print axioms binaryQuadraticMean_norm_le
end Erdos3BinaryQuadraticGauss
