import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad (α → False) → Bad (α → False)

def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun (h0 : False) => h0
| _, @Bad.mk α' h => f (α' → False) h
