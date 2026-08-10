import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad α → Bad ((α → False) → False)

def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun h0 => h0
| _, @Bad.mk α' h =>
  let recurse := f α' h
  fun (h1 : (α' → False) → False) => h1 recurse
