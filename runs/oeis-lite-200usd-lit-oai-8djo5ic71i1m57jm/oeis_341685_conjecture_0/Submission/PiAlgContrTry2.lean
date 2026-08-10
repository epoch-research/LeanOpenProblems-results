import FormalConjectures.Util.ProblemImports
open Polynomial Algebra
#check Pi.isAlgebraic
#print axioms Pi.isAlgebraic
#check Pi.algebraMap_apply
#check Polynomial.funext

noncomputable example : IsAlgebraic ℚ (fun q : ℚ => q) := by
  -- try theorem
  exact Pi.isAlgebraic (fun q : ℚ => (isAlgebraic_algebraMap q : IsAlgebraic ℚ (q : ℚ)))

noncomputable theorem piAlgFalse : False := by
  have h : IsAlgebraic ℚ (fun q : ℚ => q) := by
    exact Pi.isAlgebraic (fun q : ℚ => (isAlgebraic_algebraMap q : IsAlgebraic ℚ (q : ℚ)))
  rcases h with ⟨p, hpne, hpzero⟩
  have hroot : ∀ q : ℚ, p.eval q = 0 := by
    intro q
    have hq := congrFun hpzero q
    -- aeval_pi_apply theorem
    rw [Polynomial.aeval_pi_apply] at hq
    simpa [Polynomial.aeval_def, Polynomial.eval₂_at_apply] using hq
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro q
    simpa [hroot q]
  exact hpne hp0

#print axioms piAlgFalse
