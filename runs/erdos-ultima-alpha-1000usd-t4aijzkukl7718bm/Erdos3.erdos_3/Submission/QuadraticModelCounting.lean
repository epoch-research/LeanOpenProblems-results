import Submission.FiniteSampling

/-! Positivity of the pure quadratic four-point model. The relation count is a
squared convolution, so its lower bound follows from variance nonnegativity.
This is a model counting theorem, not a claim that an arbitrary set is governed
by a pure quadratic factor. -/
namespace Erdos3QuadraticModelCounting
open Finset Erdos3FiniteSampling
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def shiftedConvolution (f : G → ℝ) (T : G → G) (w : G) : ℝ :=
  𝔼 y : G, f (w+T y)*f y

noncomputable def balancedFourCount (f : G → ℝ) (T : G → G) : ℝ :=
  𝔼 x : G, 𝔼 y : G, 𝔼 z : G, f x*f y*f z*f (x-T y+T z)

lemma shiftedConvolution_mean (f : G → ℝ) (T : G → G) :
    (𝔼 w, shiftedConvolution f T w) = (𝔼 x, f x)^2 := by
  unfold shiftedConvolution
  rw [expect_comm]
  have hs (y : G) : (𝔼 w : G, f (w+T y)*f y) = (𝔼 x, f x)*f y := by
    rw [← expect_mul]
    congr 1
    exact Fintype.expect_equiv (Equiv.addRight (T y)) _ f (fun _ ↦ rfl)
  simp only [hs]
  rw [← mul_expect,pow_two]

lemma balancedFourCount_eq_square (f : G → ℝ) (T : G → G) :
    balancedFourCount f T = 𝔼 w, (shiftedConvolution f T w)^2 := by
  symm
  unfold shiftedConvolution balancedFourCount
  simp only [pow_two,Fintype.expect_mul_expect]
  rw [expect_comm]
  have hs (y : G) :
      (𝔼 w : G, 𝔼 z : G, (f (w+T y)*f y)*(f (w+T z)*f z)) =
      𝔼 x : G, 𝔼 z : G, f x*f y*f z*f (x-T y+T z) := by
    apply (Fintype.expect_equiv (Equiv.subRight (T y)) _ _ ?_).symm
    intro x
    apply expect_congr rfl
    intro z _
    simp only [Equiv.subRight_apply,sub_add_cancel]
    ring
  simp only [hs]
  rw [expect_comm]

/-- The model inequality needs no positivity assumption on f and no linearity
assumption on T. In the quadratic case T(y)=3y. -/
theorem balancedFourCount_lower (f : G → ℝ) (T : G → G) :
    (𝔼 x, f x)^4 ≤ balancedFourCount f T := by
  have hvar : 0 ≤ 𝔼 w : G, (shiftedConvolution f T w-𝔼 u, shiftedConvolution f T u)^2 :=
    expect_nonneg (fun _ _ ↦ sq_nonneg _)
  rw [expect_center_sq,shiftedConvolution_mean,← balancedFourCount_eq_square] at hvar
  nlinarith only [hvar]

/-- First three values of a Newton-form quadratic form bijective coordinates. -/
def quadraticValueEquiv : (G × G × G) ≃ (G × G × G) where
  toFun p := (p.1,p.1+p.2.1,p.1+2 • p.2.1+p.2.2)
  invFun p := (p.1,p.2.1-p.1,p.2.2-2 • p.2.1+p.1)
  left_inv p := by
    rcases p with ⟨a,b,c⟩
    ext <;> dsimp <;> module
  right_inv p := by
    rcases p with ⟨a,b,c⟩
    ext <;> dsimp <;> module

lemma quadraticValueEquiv_apply (p : G × G × G) :
    quadraticValueEquiv p = (p.1,p.1+p.2.1,p.1+2 • p.2.1+p.2.2) := rfl

lemma expect_triple {W : Type*} [AddCommMonoid W] [Module ℚ≥0 W] (f : G × G × G → W) :
    (𝔼 p, f p) = 𝔼 a : G, 𝔼 b : G, 𝔼 c : G, f (a,b,c) := by
  rw [show (𝔼 p, f p) = 𝔼 a : G, 𝔼 bc : G × G, f (a,bc) from expect_product _ _ _]
  apply expect_congr rfl
  intro a _
  exact expect_product _ _ _

noncomputable def quadraticModelCount (f : G → ℝ) : ℝ :=
  𝔼 a : G, 𝔼 b : G, 𝔼 c : G, f a*f (a+b)*f (a+2 • b+c)*f (a+3 • b+3 • c)

lemma quadraticModelCount_eq_balanced (f : G → ℝ) :
    quadraticModelCount f = balancedFourCount f (fun y ↦ 3 • y) := by
  have he := Fintype.expect_equiv (quadraticValueEquiv (G := G))
    (fun p : G × G × G ↦ f p.1*f (p.1+p.2.1)*f (p.1+2 • p.2.1+p.2.2)*f (p.1+3 • p.2.1+3 • p.2.2))
    (fun p : G × G × G ↦ f p.1*f p.2.1*f p.2.2*f (p.1-3 • p.2.1+3 • p.2.2)) (by
      rintro ⟨a,b,c⟩
      rw [quadraticValueEquiv_apply]
      dsimp only
      congr 2
      module)
  simpa only [expect_triple] using he

/-- Uniform independent quadratic coefficients give at least the random-model
four-point count. Additional structural hypotheses are needed to apply this to
arbitrary functions on an arithmetic progression. -/
theorem quadraticModelCount_lower (f : G → ℝ) : (𝔼 x, f x)^4 ≤ quadraticModelCount f := by
  rw [quadraticModelCount_eq_balanced]
  exact balancedFourCount_lower f _

#print axioms balancedFourCount_lower
#print axioms quadraticModelCount_lower
end Erdos3QuadraticModelCounting
