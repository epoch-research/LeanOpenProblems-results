import FormalConjectures.Util.ProblemImports
open Polynomial Algebra
noncomputable instance : Algebra (Polynomial ℚ) (ℚ → ℚ) := Polynomial.instAlgebraPi

#check IsAlgebraic.restrictScalars
#check IsAlgebraic.tower_top
#check IsAlgebraic.extendScalars
#check IsAlgebraic.of_algebraicAlgHom
#check Algebra.IsAlgebraic.trans
#check Algebra.IsAlgebraic.tower_top
#check Algebra.IsAlgebraic.of_ringHom_of_comp_eq

noncomputable example : IsAlgebraic (Polynomial ℚ) (fun q : ℚ => q) := by
  refine ⟨Polynomial.X - Polynomial.C Polynomial.X, ?_, ?_⟩
  · intro h
    have hc := congrArg Polynomial.natDegree h
    simp at hc
  · ext q
    simp [Polynomial.aeval_polynomial_pi, aevalAeval]

noncomputable example : IsAlgebraic ℚ (fun q : ℚ => q) := by
  have hPX : IsAlgebraic (Polynomial ℚ) (fun q : ℚ => q) := by
    refine ⟨Polynomial.X - Polynomial.C Polynomial.X, ?_, ?_⟩
    · intro h
      have hc := congrArg Polynomial.natDegree h
      simp at hc
    · ext q
      simp [Polynomial.aeval_polynomial_pi, aevalAeval]
  -- try suggestions
  exact IsAlgebraic.restrictScalars ℚ hPX
