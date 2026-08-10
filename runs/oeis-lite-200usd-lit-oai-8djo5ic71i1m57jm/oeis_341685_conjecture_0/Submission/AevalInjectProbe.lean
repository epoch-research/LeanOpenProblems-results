import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check Polynomial.aeval
#check Polynomial.aeval_algHom
#check Polynomial.aeval_X
#check transcendental_iff_injective
#check isAlgebraic_iff_not_injective
example : Function.Injective (Polynomial.aeval xi_3 : Polynomial ℚ →ₐ[ℚ] Padic 3) := by
  apply?
example : ¬ IsAlgebraic ℚ xi_3 := by
  rw [← transcendental_iff]
  rw [transcendental_iff_injective]
  apply?
