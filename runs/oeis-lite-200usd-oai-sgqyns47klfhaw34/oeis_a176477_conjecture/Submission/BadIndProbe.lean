import FormalConjectures.Util.ProblemImports
inductive Bad : Prop where
| mk : (Bad -> False) -> Bad

def f (b : Bad) : False := match b with | Bad.mk h => h b
example : False := f (Bad.mk f)
