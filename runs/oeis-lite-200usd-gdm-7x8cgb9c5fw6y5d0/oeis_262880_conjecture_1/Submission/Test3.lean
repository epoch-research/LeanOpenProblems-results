import FormalConjectures.Util.ProblemImports

def my_true_imp : True := True.intro

@[implemented_by my_true_imp]
def my_true : True := sorry

#print axioms my_true
