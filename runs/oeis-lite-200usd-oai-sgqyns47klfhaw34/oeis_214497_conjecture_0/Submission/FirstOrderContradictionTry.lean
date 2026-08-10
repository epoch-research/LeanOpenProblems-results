import FormalConjectures.Util.ProblemImports

open FirstOrder

#print FirstOrder.Language.Theory.IsSatisfiable
#print FirstOrder.Language.Theory.CompleteType.false_of_mem_of_not_mem
#check FirstOrder.Language.Theory.CompleteType.false_of_mem_of_not_mem

example : False := by
  let L : FirstOrder.Language := ⊥
  let T : L.Theory := Set.univ
  apply FirstOrder.Language.Theory.CompleteType.false_of_mem_of_not_mem (T := T)
  · -- satisfiable?
    simp [FirstOrder.Language.Theory.IsSatisfiable, T]
  · simp [T]
  · simp [T]
