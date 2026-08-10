import FormalConjectures.Util.ProblemImports

open Polynomial Algebra

#check Algebra.IsAlgebraic.pi
#check IsAlgebraic.pi
#check Polynomial.funext
#check Polynomial.eq_zero_of_infinite_roots
#check Polynomial.roots
#check Polynomial.mem_roots
#check Polynomial.eval₂_eq_eval_map
#check Polynomial.aeval_eq_eval
#check Polynomial.aeval_def
#check Polynomial.eval₂_at_apply
#check Polynomial.aeval_pi_apply
#check Polynomial.eval₂_eq_eval_map

example : False := by
  have h : IsAlgebraic ℚ (fun q : ℚ => q) := by infer_instance
  rcases h with ⟨p, hpne, hpzero⟩
  have hroot : ∀ q : ℚ, p.eval q = 0 := by
    intro q
    have := congrFun hpzero q
    -- hpzero : aeval (fun q => q) p = 0 as functions
    simpa [Polynomial.aeval_def] using this
  have hp0 : p = 0 := by
    -- polynomial over integral domain with all rationals roots
    apply Polynomial.eq_zero_of_infinite_roots
    intro q
    simpa [hroot q]
  exact hpne hp0

#print axioms PiAlgContrTry._example_1
