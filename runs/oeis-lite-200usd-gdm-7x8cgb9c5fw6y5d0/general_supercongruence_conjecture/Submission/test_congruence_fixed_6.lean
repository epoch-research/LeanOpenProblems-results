import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk {β : Prop} : Bad α (β → False) → Bad α (((β → False) → False) → False)

def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h =>
  let recurse := f α (β' → False) h
  fun (h2 : (β' → False) → False) => h2 recurse
