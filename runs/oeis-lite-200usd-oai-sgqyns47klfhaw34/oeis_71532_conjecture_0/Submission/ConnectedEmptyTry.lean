import FormalConjectures.Util.ProblemImports
#print ConnectedSpace
#check ConnectedSpace.toNonempty
#print IrreducibleSpace
#check IrreducibleSpace.toNonempty

example : False := by
  letI : TopologicalSpace Empty := inferInstance
  letI : ConnectedSpace Empty := by
    constructor
    -- inspect goals
    all_goals simp [isPreconnected_univ]
  have h : Nonempty Empty := ConnectedSpace.toNonempty Empty
  exact h.elim (by intro x; cases x)
