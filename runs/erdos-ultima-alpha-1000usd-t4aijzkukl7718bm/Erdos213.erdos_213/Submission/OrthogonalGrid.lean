import Submission.OrthogonalGlobal
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Geometric application of the completed rational-square descent.
This excludes an orthogonal grid source, not arbitrary configurations. -/
namespace Erdos213.OrthogonalGrid
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem no_four_rational_norms {p q : E} (hp : p ≠ 0) (hq : q ≠ 0)
    (ho : inner ℝ p q = 0)
    (h1 : ‖p‖ ∈ Set.range ((↑) : ℚ → ℝ))
    (h2 : ‖q‖ ∈ Set.range ((↑) : ℚ → ℝ))
    (h3 : ‖p+q‖ ∈ Set.range ((↑) : ℚ → ℝ))
    (h4 : ‖p+(2 : ℝ) • q‖ ∈ Set.range ((↑) : ℚ → ℝ)) : False := by
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  obtain ⟨c,hc⟩ := h3
  obtain ⟨d,hd⟩ := h4
  have ha0 : a ≠ 0 := by
    intro hz
    have hh : ‖p‖=0 := by simpa [hz] using ha.symm
    exact hp (norm_eq_zero.mp hh)
  have hb0 : b ≠ 0 := by
    intro hz
    have hh : ‖q‖=0 := by simpa [hz] using hb.symm
    exact hq (norm_eq_zero.mp hh)
  have he1 : c^2=a^2+b^2 := by
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_real ho
    rw [← ha,← hb,← hc] at hh
    have hh' : c*c=a*a+b*b := by exact_mod_cast hh
    simpa only [pow_two] using hh'
  have he2 : d^2=a^2+4*b^2 := by
    have hh : ‖p+(2 : ℝ) • q‖^2=‖p‖^2+4*‖q‖^2 := by
      rw [norm_add_sq_real,inner_smul_right,ho,norm_smul]
      norm_num
      ring
    rw [← ha,← hb,← hd] at hh
    exact_mod_cast hh
  apply OrthogonalGlobal.no_simultaneous_squares (div_ne_zero ha0 hb0)
  constructor
  · refine ⟨c/b,?_⟩
    field_simp
    nlinarith [he1]
  · refine ⟨d/b,?_⟩
    field_simp
    nlinarith [he2]

#print axioms no_four_rational_norms
end Erdos213.OrthogonalGrid
