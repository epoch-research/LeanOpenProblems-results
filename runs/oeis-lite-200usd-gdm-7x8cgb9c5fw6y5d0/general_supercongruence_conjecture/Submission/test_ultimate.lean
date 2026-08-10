import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad True
| mk {α : Prop} : Bad ((α → False) → False) → Bad α

open Classical

noncomputable def f : (α : Prop) → Bad α → α
| _, Bad.base => True.intro
| _, @Bad.mk α' h =>
  let recurse := f ((α' → False) → False) h
  Classical.byContradiction recurse
