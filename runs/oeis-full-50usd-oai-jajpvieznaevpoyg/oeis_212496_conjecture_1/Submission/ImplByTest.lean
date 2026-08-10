import FormalConjectures.Util.ProblemImports

def t_impl : True := True.intro
@[implemented_by t_impl]
def t_bad : False := by
  contradiction
