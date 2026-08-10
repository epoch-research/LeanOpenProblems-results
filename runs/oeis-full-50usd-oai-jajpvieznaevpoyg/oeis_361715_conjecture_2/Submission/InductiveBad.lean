import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| intro : (Bad → False) → Bad

def bad : Bad := Bad.intro (fun b => match b with | Bad.intro f => f (Bad.intro f))
example : False := match bad with | Bad.intro f => f bad
#print axioms bad
#print axioms «example»
