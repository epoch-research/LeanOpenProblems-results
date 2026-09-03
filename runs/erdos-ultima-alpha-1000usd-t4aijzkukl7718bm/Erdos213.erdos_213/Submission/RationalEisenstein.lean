import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Rational arithmetic in Q(sqrt(-3)), with its complex embedding. -/
namespace Erdos213.RationalEisenstein
open scoped QuadraticAlgebra

abbrev G := QuadraticAlgebra ℚ (-3) 0
instance : Fact (∀ r : ℚ, r^2 ≠ -3+0*r) := ⟨by intro r; nlinarith [sq_nonneg r]⟩
abbrev rr : G := QuadraticAlgebra.omega

lemma rr_sq : rr^2 = -3 := by
  rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> norm_num [QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg]

-- The extra zero-preservation makes division and inversion available to simp.
def norm : G →*₀ ℚ :=
  { QuadraticAlgebra.norm with map_zero' := QuadraticAlgebra.norm_zero }

lemma norm_components (z : G) : norm z = z.re^2+3*z.im^2 := by
  change z.re*z.re+0*z.re*z.im-(-3)*z.im*z.im = _
  ring

lemma norm_rr : norm rr = 3 := by norm_num [norm_components,rr]
lemma norm_ne_zero {z : G} (hz : z ≠ 0) : norm z ≠ 0 :=
  fun h => hz (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)

noncomputable def rho : ℂ := (Real.sqrt 3 : ℂ)*Complex.I
lemma rho_sq : rho^2 = -3 := by
  have hs : (Real.sqrt 3 : ℂ)^2=3 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [rho,mul_pow,Complex.I_sq,hs]
  ring

noncomputable def toComplex : G →+* ℂ where
  toFun z := (z.re : ℂ)+(z.im : ℂ)*rho
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,Rat.cast_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
    push_cast
    ring_nf
    simp only [rho_sq]
    ring

lemma toComplex_injective : Function.Injective toComplex := toComplex.injective

lemma normSq_toComplex (z : G) : Complex.normSq (toComplex z) = (norm z : ℝ) := by
  rw [norm_components]
  simp [toComplex,rho,Complex.normSq_apply]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination (z.im : ℝ)^2*hs

lemma dist_sq (z w : G) : dist (toComplex z) (toComplex w)^2 = (norm (z-w) : ℝ) := by
  rw [dist_eq_norm, ← map_sub, ← Complex.normSq_eq_norm_sq, normSq_toComplex]

#print axioms normSq_toComplex
#print axioms dist_sq
end Erdos213.RationalEisenstein
