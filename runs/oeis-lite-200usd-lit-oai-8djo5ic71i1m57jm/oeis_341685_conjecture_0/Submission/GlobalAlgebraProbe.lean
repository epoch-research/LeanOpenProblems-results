import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra
#check Algebra.IsAlgebraic
#check Algebra.Transcendental
#check Algebra.transcendental_iff_not_isAlgebraic
#check isAlgebraic_iff_not_injective
#check Transcendental
#check Algebraic.countable
#synth CharZero (Padic 3)
#synth FaithfulSMul ℚ (Padic 3)
#synth Module.IsTorsionFree ℚ (Padic 3)
#check Subalgebra.isAlgebraic_of_isAlgebraic_bot
#check Subalgebra.isAlgebraic_bot_iff
#check (⊥ : Subalgebra ℚ (Padic 3))
#check Subalgebra.mem_bot
#check Algebra.mem_bot
example (x : Padic 3) : IsAlgebraic ℚ x := by
  apply?
example (x : Padic 3) : ¬ IsAlgebraic ℚ x := by
  apply?
