import FormalConjectures.Util.ProblemImports
open SimpleGraph

example : False := by
  let s : {s : Finset (Fin 2) // #s = 1} := ⟨{0}, by simp⟩
  let t : {s : Finset (Fin 2) // #s = 1} := ⟨{1}, by simp⟩
  have h := johnson_adj_iff_ge (n := 2) (k := 1) (s := s) (t := t)
  -- In J(2,1), disjoint singletons are adjacent? Standard if intersection size k-1=0 yes.
  guard_target = False
  sorry
