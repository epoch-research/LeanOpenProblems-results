import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3 : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
open Algebra

#check Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim
#print axioms Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim
#check FreeGroup.reduce.not
#check FreeAddGroup.reduce.not
#check Std.Do.SPred.pure_intro
#check Std.Do.SPred.pure_elim'
#check Std.Do.SPred.pure_congr

example : False := by
  refine Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim (α := PUnit) ?_ ?_
  · intro h; exact ?a
  · intro hn; exact false_of_nontrivial_of_subsingleton PUnit

example : IsAlgebraic ℚ xi_3 := by
  refine Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim (α := IsAlgebraic ℚ xi_3) ?_ ?_
  · intro hsub
    -- hsub is always true, but does not give existence
    exact ?a
  · intro hnon
    rcases hnon with ⟨h1, h2, _⟩
    exact h1

example : False := by
  exact FreeGroup.reduce.not (p := False) (by native_decide : FreeGroup.reduce ([] : List (PUnit × Bool)) = [] ++ [(PUnit.unit, true), (PUnit.unit, false)] ++ [])
