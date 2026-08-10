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
  if h_alpha' : α' then
    let recurse := f (N2 α') h
    (fun h_0_0 => (recurse (fun h_1_2 => (recurse (fun h_1_4 => (recurse (fun h_1_6 => (recurse (fun h_1_8 => (recurse (fun h_1_10 => (recurse (fun h_1_12 => (recurse (fun h_1_14 => (recurse (fun h_1_16 => (recurse (fun h_1_18 => (recurse (fun h_1_20 => (recurse (fun h_1_22 => (recurse (fun h_1_24 => (recurse (fun h_1_26 => (recurse (fun h_1_28 => (h_1_2 h_0_0))))))))))))))))))))))))))))))
  else
    h_alpha'

