import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False

inductive Bad : Prop → Prop where
| base {α : Prop} : N1 α → Bad α
| mk {α : Prop} : Bad (N2 α) → Bad (N0 α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N1 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  let recurse := f (N2 α') h
  fun (h0 : α') => (Classical.byContradiction recurse) h0
