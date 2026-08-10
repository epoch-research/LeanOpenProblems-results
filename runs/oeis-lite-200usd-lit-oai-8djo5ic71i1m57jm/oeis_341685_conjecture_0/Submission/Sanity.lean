import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

example : (0 : Padic 3) ≠ 1 := by norm_num
example : Function.Injective (algebraMap ℚ (Padic 3)) := by infer_instance
example : (algebraMap ℚ (Padic 3) (1 : ℚ)) = 1 := by simp
example : IsAlgebraic ℚ (0 : Padic 3) := isAlgebraic_zero
example : ¬ Subsingleton (Padic 3) := by
  intro h
  have := (Subsingleton.elim (0 : Padic 3) 1)
  norm_num at this
