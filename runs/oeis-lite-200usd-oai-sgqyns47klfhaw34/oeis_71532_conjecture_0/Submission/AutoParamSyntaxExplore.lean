import FormalConjectures.Util.ProblemImports

#check autoParam
macro "my_tac" : tactic => `(tactic| exact trivial)

def g (h : autoParam True my_tac) : True := h
#check g
example : True := g
