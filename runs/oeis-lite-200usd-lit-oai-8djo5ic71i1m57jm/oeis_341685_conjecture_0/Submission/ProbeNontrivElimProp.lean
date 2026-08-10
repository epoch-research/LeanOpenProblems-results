import FormalConjectures.Util.ProblemImports

#check Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim

example : False := by
  refine Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim (α := False) ?_ ?_
  · intro hsub
    -- hsub : Subsingleton False, no inhabitant
    exact False.elim ?missing
  · intro hnon
    exact false_of_nontrivial_of_subsingleton False

example (P : Prop) : P := by
  refine Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim (α := P) ?_ ?_
  · intro hsub
    -- no P
    sorry
  · intro hnon
    haveI := hnon
    haveI : Subsingleton P := subsingleton_Prop
    exact False.elim (false_of_nontrivial_of_subsingleton P)
