import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk1 {β : Prop} : Bad α (β → False) → Bad α (((β → False) → False) → False)
| mk2 {β : Prop} : Bad α ((β → False) → False) → Bad α β

open Classical

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk1 _ β' h =>
  let recurse := f α (β' → False) h
  fun (h2 : (β' → False) → False) => h2 recurse
| _, @Bad.mk2 _ β' h =>
  let recurse := f α ((β' → False) → False) h
  Classical.byContradiction recurse
