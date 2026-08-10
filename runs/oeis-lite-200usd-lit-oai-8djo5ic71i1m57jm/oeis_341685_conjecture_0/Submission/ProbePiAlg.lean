import FormalConjectures.Util.ProblemImports
open Polynomial Algebra

#check Pi.isAlgebraic
#check Pi.algebraMap_apply
#check Algebra.IsAlgebraic.pi
#check IsAlgebraic.pi
#synth Algebra.IsAlgebraic ℚ (ℚ → ℚ)
#check (inferInstance : Algebra.IsAlgebraic ℚ (ℚ → ℚ))

example : IsAlgebraic ℚ (fun q : ℚ => q) := by
  infer_instance

example : False := by
  have h : IsAlgebraic ℚ (fun q : ℚ => q) := by infer_instance
  rcases h with ⟨p, hpne, hpzero⟩
  -- evaluate polynomial equality at more roots? Need show p has infinite roots -> p=0
  guard_target = False
  sorry
