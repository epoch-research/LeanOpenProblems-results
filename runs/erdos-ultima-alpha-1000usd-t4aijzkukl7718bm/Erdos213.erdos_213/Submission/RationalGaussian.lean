import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Rational Gaussian arithmetic, with an explicit bridge to complex norms. -/
namespace Erdos213.RationalGaussian

abbrev G := QuadraticAlgebra ℚ (-1) 0

instance : Fact (∀ r : ℚ, r^2 ≠ -1+0*r) := ⟨by intro r; nlinarith [sq_nonneg r]⟩

abbrev ii : G := QuadraticAlgebra.omega

lemma ii_sq : ii^2 = -1 := by
  change (QuadraticAlgebra.omega : G)^2 = -1
  rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rfl

def norm : G →*₀ ℚ :=
  { QuadraticAlgebra.norm with map_zero' := QuadraticAlgebra.norm_zero }

lemma norm_components (z : G) : norm z = z.re^2+z.im^2 := by
  change z.re*z.re+0*z.re*z.im-(-1)*z.im*z.im = _
  ring

lemma norm_ii : norm ii = 1 := by norm_num [norm_components,ii]

lemma norm_ne_zero {z : G} (hz : z ≠ 0) : norm z ≠ 0 := by
  exact fun h => hz (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp h)

noncomputable def toComplex : G →+* ℂ where
  toFun z := (z.re : ℂ)+(z.im : ℂ)*Complex.I
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, Rat.cast_add]
    ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma toComplex_injective : Function.Injective toComplex := toComplex.injective

lemma normSq_toComplex (z : G) : Complex.normSq (toComplex z) = (norm z : ℝ) := by
  rw [norm_components]
  simp [toComplex,Complex.normSq_apply]
  ring

lemma dist_sq (z w : G) : dist (toComplex z) (toComplex w)^2 = (norm (z-w) : ℝ) := by
  rw [dist_eq_norm, ← map_sub, ← Complex.normSq_eq_norm_sq, normSq_toComplex]

#print axioms normSq_toComplex
#print axioms dist_sq
end Erdos213.RationalGaussian
