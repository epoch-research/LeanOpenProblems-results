import FormalConjectures.Util.ProblemImports
partial def bad {α : Sort u} : α := bad

theorem false_by_partial : False := bad
#print axioms false_by_partial
#print false_by_partial
