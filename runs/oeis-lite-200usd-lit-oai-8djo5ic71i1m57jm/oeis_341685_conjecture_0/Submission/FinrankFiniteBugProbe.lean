import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra Module

#check Module.finrank_pos
#check Module.finite_of_finrank_pos
#synth Module.IsTorsionFree ℚ (Padic 3)
#synth Nontrivial (Padic 3)
#check (Module.finrank_pos (R := ℚ) (M := Padic 3))

example : Module.Finite ℚ (Padic 3) := by
  exact Module.finite_of_finrank_pos (Module.finrank_pos (R := ℚ) (M := Padic 3))

example : IsAlgebraic ℚ xi_3 := by
  haveI : Module.Finite ℚ (Padic 3) := Module.finite_of_finrank_pos (Module.finrank_pos (R := ℚ) (M := Padic 3))
  exact IsAlgebraic.of_finite ℚ xi_3

example : ¬ (¬ IsAlgebraic ℚ xi_3) := by
  exact not_not_intro (by
    haveI : Module.Finite ℚ (Padic 3) := Module.finite_of_finrank_pos (Module.finrank_pos (R := ℚ) (M := Padic 3))
    exact IsAlgebraic.of_finite ℚ xi_3)
