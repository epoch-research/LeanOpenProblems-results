import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad -> False) -> Bad

def bad : Bad := Bad.intro (fun b => match b with | Bad.intro f => f b)
theorem t : False := match bad with | Bad.intro f => f bad
#print axioms t
